//! Module names (ch08 R1, R24) and the module graph (ch08 R7, R8): use
//! paths resolved to modules by the longest-module-prefix rule, and
//! cycle/self-import detection. Since owner decision 2026-09-19 round 5
//! (D3) the edge set is EXACTLY the explicit `use` edges of the file
//! headers: there is no implicit prelude-module edge and no scan of a
//! file's body, so a build's dependency graph is readable from headers
//! alone (ch08 R7).
//!
//! Building a file's canonical name and extracting its header/`use` paths
//! is per-file work (`extract_module_facts`); linking those facts across
//! every file of a build into one graph (`build_module_graph`) is
//! necessarily a whole-build step, since ch08 R4's "is this prefix a
//! module" test depends on the full module-name set.

use fors_lex::{TokenKind, Tokens, keyword_kind};
use fors_syntax::{NodeKind, Tree};
use std::collections::HashMap;

use crate::diag::{DiagCode, Diagnostic};
use crate::ids::{FileId, ModuleId};
use crate::interner::{Interner, Symbol};

pub type Segments = Vec<Symbol>;

/// Ch08 R24: a legal directory segment or file stem — `[a-z_][a-z0-9_]*`,
/// not `_` alone, not a reserved word (contextual keywords lex as `Ident`
/// and so are legal here; only ch07's reserved set is excluded).
pub fn is_legal_segment(bytes: &[u8]) -> bool {
    if bytes.is_empty() || bytes == b"_" {
        return false;
    }
    let first_ok = bytes[0] == b'_' || bytes[0].is_ascii_lowercase();
    if !first_ok {
        return false;
    }
    if !bytes
        .iter()
        .all(|&b| b == b'_' || b.is_ascii_lowercase() || b.is_ascii_digit())
    {
        return false;
    }
    keyword_kind(bytes).is_none()
}

/// Ch08 R1: joins `package` (already-validated manifest segments) and
/// `path` (directory segments then file stem, all relative to the source
/// root) into one module name. `Err(i)` names the illegal `path` segment.
pub fn module_segments(
    interner: &mut Interner,
    package: &[&[u8]],
    path: &[&[u8]],
) -> Result<Segments, usize> {
    for (i, seg) in path.iter().enumerate() {
        if !is_legal_segment(seg) {
            return Err(i);
        }
    }
    Ok(package
        .iter()
        .chain(path.iter())
        .map(|s| interner.intern(s))
        .collect())
}

pub fn segments_eq(a: &[Symbol], b: &[Symbol]) -> bool {
    a == b
}

pub fn join_dotted(interner: &Interner, segs: &[Symbol]) -> String {
    let mut out = String::new();
    for (i, &s) in segs.iter().enumerate() {
        if i > 0 {
            out.push('.');
        }
        out.push_str(&String::from_utf8_lossy(interner.resolve(s)));
    }
    out
}

fn is_sig(tokens: &Tokens, i: usize) -> bool {
    !tokens.kinds[i].is_trivia()
}

fn byte_range(tree: &Tree, tokens: &Tokens, node: usize) -> (u32, u32) {
    let (a, b) = tree.token_range(node);
    let start = tokens.range(a as usize).0;
    let end = if b > a {
        tokens.range(b as usize - 1).1
    } else {
        start
    };
    (start, end)
}

/// Reads the dotted identifier segments directly owned by a `Path` node
/// (`ident { "." ident }`, ch08 R3).
fn path_segments(
    tree: &Tree,
    tokens: &Tokens,
    source: &[u8],
    interner: &mut Interner,
    path_node: usize,
) -> Segments {
    let (first, end) = tree.token_range(path_node);
    let mut segs = Vec::new();
    let mut i = first as usize;
    let end = end as usize;
    while i < end {
        if is_sig(tokens, i) && tokens.kinds[i] == TokenKind::Ident {
            segs.push(interner.intern(tokens.text(i, source)));
        }
        i += 1;
    }
    segs
}

/// Everything one file contributes to the module graph: its `module`
/// header (if any, with the path's byte range for a mismatch diagnostic)
/// and every `use` path with its byte range.
pub struct FileFacts {
    pub header: Option<(Segments, (u32, u32))>,
    pub uses: Vec<(Segments, (u32, u32))>,
}

/// Per-file extraction: depends only on this file's tree/tokens.
pub fn extract_module_facts(
    tree: &Tree,
    tokens: &Tokens,
    source: &[u8],
    interner: &mut Interner,
) -> FileFacts {
    let mut header = None;
    let mut uses = Vec::new();
    if !tree.is_empty() {
        for child in tree.children(0) {
            match tree.kinds[child] {
                NodeKind::ModuleHdr => {
                    if let Some(path_node) = tree.children(child).next() {
                        let segs = path_segments(tree, tokens, source, interner, path_node);
                        header = Some((segs, byte_range(tree, tokens, path_node)));
                    }
                }
                NodeKind::UseDecl => {
                    // Each child is a `UseItem` (ch07 grammar, D2); its
                    // only child is the `path`. An alias ("as" ident) does
                    // not change the module-graph edge (ch08 R3), so it is
                    // not read here; the resolver reads it from the tree
                    // directly to decide the bound name (ch08 R4).
                    for use_item in tree.children(child) {
                        if let Some(path_node) = tree.children(use_item).next() {
                            let segs = path_segments(tree, tokens, source, interner, path_node);
                            uses.push((segs, byte_range(tree, tokens, path_node)));
                        }
                    }
                }
                _ => {}
            }
        }
    }
    FileFacts { header, uses }
}

pub struct ModuleTable {
    pub file: Vec<FileId>,
    pub name: Vec<Segments>,
    /// Lookup only, never iterated: ids and diagnostics come from the
    /// index-ordered columns above.
    by_name: HashMap<Segments, ModuleId>,
}

impl ModuleTable {
    pub fn len(&self) -> usize {
        self.file.len()
    }

    pub fn is_empty(&self) -> bool {
        self.file.is_empty()
    }

    pub fn find(&self, segs: &[Symbol]) -> Option<ModuleId> {
        self.by_name.get(segs).copied()
    }
}

struct Edge {
    from: ModuleId,
    to: ModuleId,
    range: (u32, u32),
}

/// Builds the module table, resolves every file's header/`use` facts into
/// graph edges, and checks self-import and cycles (ch08 R7, R8). `files`
/// pairs each module's canonical name with its per-file facts, in
/// whatever order the caller indexed files; the result is independent of
/// that order (edges are deduplicated and sorted before cycle search).
pub fn build_module_graph(
    interner: &Interner,
    files: Vec<(FileId, Segments, FileFacts)>,
) -> (ModuleTable, Vec<(ModuleId, ModuleId)>, Vec<Diagnostic>) {
    let mut diags = Vec::new();
    let mut table = ModuleTable {
        file: Vec::new(),
        name: Vec::new(),
        by_name: HashMap::new(),
    };
    for (i, (fid, name, _)) in files.iter().enumerate() {
        table.file.push(*fid);
        table.name.push(name.clone());
        // Two files mapping to one name (Rule 24) is the caller's build
        // error; the first keeps the name so ids stay order-stable.
        table
            .by_name
            .entry(name.clone())
            .or_insert(ModuleId(i as u32));
    }
    let by_name = &table.by_name;

    // Rule 1: header path must equal the file's derived name.
    for (m, (_, name, facts)) in files.iter().enumerate() {
        if let Some((header_segs, range)) = &facts.header
            && !segments_eq(header_segs, name)
        {
            let got = join_dotted(interner, header_segs);
            let want = join_dotted(interner, name);
            diags.push(Diagnostic::new(
                table.file[m],
                range.0,
                range.1,
                DiagCode::HeaderPathMismatch,
                format!("module header `{got}` does not match its file's module name `{want}`"),
            ));
        }
    }

    let mut edges: Vec<Edge> = Vec::new();
    for (m, (_, _, facts)) in files.iter().enumerate() {
        let from = ModuleId(m as u32);
        for (path, range) in &facts.uses {
            resolve_use_edge(
                by_name,
                from,
                table.file[m],
                path,
                *range,
                &mut edges,
                &mut diags,
                interner,
            );
        }
    }

    edges.sort_by_key(|a| (a.from, a.to));
    edges.dedup_by(|a, b| a.from == b.from && a.to == b.to);

    let cycle_diags = detect_cycles(&table, &edges, interner);
    diags.extend(cycle_diags);

    let pairs = edges.iter().map(|e| (e.from, e.to)).collect();
    (table, pairs, diags)
}

fn push_edge_dedup(edges: &mut Vec<Edge>, e: Edge) {
    if !edges.iter().any(|x| x.from == e.from && x.to == e.to) {
        edges.push(e);
    }
}

/// Ch08 R4: the longest-module-prefix rule. The whole path names a
/// module (case a); otherwise, if it has at least two segments and its
/// first `n-1` segments name a module, the edge targets that module
/// (case b, an item import); otherwise the path is left unresolved (no
/// edge) — this crate does not perform Rule 4(c)'s unresolved-import
/// check, which needs full item visibility, not just the module set.
/// A cycle found in the module graph (ch08 Rule 7): the modules on it, in
/// order, and the byte range of the `use` path that forms each edge, so the
/// diagnostic can point at the imports rather than at the modules.
type Cycle = (Vec<usize>, Vec<(u32, u32)>);

fn resolve_use_edge(
    by_name: &HashMap<Segments, ModuleId>,
    from: ModuleId,
    from_file: FileId,
    path: &[Symbol],
    range: (u32, u32),
    edges: &mut Vec<Edge>,
    diags: &mut Vec<Diagnostic>,
    interner: &Interner,
) {
    let target = if let Some(&m) = by_name.get(path) {
        Some(m)
    } else if path.len() >= 2 {
        by_name.get(&path[..path.len() - 1]).copied()
    } else {
        None
    };
    let Some(to) = target else { return };
    if to == from {
        let name = join_dotted(interner, path);
        diags.push(Diagnostic::new(
            from_file,
            range.0,
            range.1,
            DiagCode::SelfImport,
            format!("module imports itself via `{name}`"),
        ));
        return;
    }
    push_edge_dedup(edges, Edge { from, to, range });
}

/// Finds and reports each cycle as one diagnostic (ch08 R7), then removes
/// its closing edge and repeats until the graph is acyclic. Traversal
/// order is always modules-by-name then edges-by-target-name, so the
/// reported cycle and its starting module (the lexicographically least
/// on it) are deterministic regardless of input file order.
fn detect_cycles(table: &ModuleTable, edges: &[Edge], interner: &Interner) -> Vec<Diagnostic> {
    let n = table.len();
    let mut adj: Vec<Vec<(ModuleId, (u32, u32))>> = vec![Vec::new(); n];
    for e in edges {
        adj[e.from.index()].push((e.to, e.range));
    }
    let name_bytes: Vec<Vec<u8>> = table
        .name
        .iter()
        .map(|s| join_dotted(interner, s).into_bytes())
        .collect();
    for adj_list in &mut adj {
        adj_list.sort_by(|a, b| name_bytes[a.0.index()].cmp(&name_bytes[b.0.index()]));
    }

    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| name_bytes[a].cmp(&name_bytes[b]));

    let mut out = Vec::new();
    let max_iters = edges.len() + 1;
    for _ in 0..max_iters {
        let Some(found) = find_one_cycle(&adj, &order) else {
            break;
        };
        let (path, path_edges) = found;
        // Rotate so the lexicographically least module starts the cycle.
        let min_pos = (0..path.len())
            .min_by_key(|&i| &name_bytes[path[i]])
            .unwrap_or(0);
        let mut names = String::new();
        for k in 0..=path.len() {
            if k > 0 {
                names.push_str(" -> ");
            }
            let idx = path[(min_pos + k) % path.len()];
            names.push_str(&join_dotted(interner, &table.name[idx]));
        }
        // Edge that closes the cycle back to the starting (least) module.
        let closing_idx = (min_pos + path.len() - 1) % path.len();
        let closing_edge = path_edges[closing_idx];
        out.push(Diagnostic::new(
            table.file[path[closing_idx]],
            closing_edge.0,
            closing_edge.1,
            DiagCode::ImportCycle,
            format!("import cycle: {names}"),
        ));
        // Remove that edge so the next iteration searches the rest of the graph.
        let tail = path[closing_idx];
        let head = path[min_pos];
        adj[tail].retain(|&(to, _)| to != ModuleId(head as u32));
    }
    out
}

/// One DFS over `order` (modules) and each node's `adj` (already sorted
/// by target name) looking for the first back edge; returns the cycle as
/// a list of module indices (in discovery order, not yet rotated) plus,
/// parallel to it, the edge range used to reach each successor.
fn find_one_cycle(adj: &[Vec<(ModuleId, (u32, u32))>], order: &[usize]) -> Option<Cycle> {
    let n = adj.len();
    let mut visited = vec![false; n];
    for &start in order {
        if visited[start] {
            continue;
        }
        let mut on_stack = vec![false; n];
        let mut stack: Vec<usize> = Vec::new();
        let mut edge_in: Vec<(u32, u32)> = Vec::new();
        if let Some(result) = dfs(
            start,
            adj,
            &mut visited,
            &mut on_stack,
            &mut stack,
            &mut edge_in,
        ) {
            return Some(result);
        }
    }
    None
}

fn dfs(
    u: usize,
    adj: &[Vec<(ModuleId, (u32, u32))>],
    visited: &mut [bool],
    on_stack: &mut [bool],
    stack: &mut Vec<usize>,
    edge_in: &mut Vec<(u32, u32)>,
) -> Option<Cycle> {
    visited[u] = true;
    on_stack[u] = true;
    stack.push(u);
    for &(v, range) in &adj[u] {
        let v = v.index();
        if on_stack[v] {
            let pos = stack.iter().position(|&x| x == v).unwrap_or(0);
            // ranges[i] is the edge path[i] -> path[i+1 mod len]: edge_in[pos..]
            // covers path[0]->path[1] .. path[len-2]->path[len-1], and the just-found
            // back edge closes path[len-1] -> path[0].
            let path = stack[pos..].to_vec();
            let mut ranges = edge_in[pos..].to_vec();
            ranges.push(range);
            return Some((path, ranges));
        }
        if !visited[v] {
            edge_in.push(range);
            if let Some(r) = dfs(v, adj, visited, on_stack, stack, edge_in) {
                return Some(r);
            }
            edge_in.pop();
        }
    }
    stack.pop();
    on_stack[u] = false;
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use fors_syntax::parse_file;

    fn facts(interner: &mut Interner, src: &str) -> FileFacts {
        let p = parse_file(src.as_bytes());
        extract_module_facts(&p.tree, &p.tokens, src.as_bytes(), interner)
    }

    #[test]
    fn legal_segment_rules() {
        assert!(is_legal_segment(b"img"));
        assert!(is_legal_segment(b"a1"));
        assert!(!is_legal_segment(b"_"));
        assert!(!is_legal_segment(b"Img"));
        assert!(!is_legal_segment(b"fn"));
        assert!(!is_legal_segment(b""));
    }

    #[test]
    fn header_mismatch_detected() {
        let mut interner = Interner::new();
        let facts = facts(&mut interner, "module wrong;\n");
        let name = module_segments(&mut interner, &[], &[b"right"]).unwrap();
        let (_, edges, diags) = build_module_graph(&interner, vec![(FileId(0), name, facts)]);
        assert!(edges.is_empty());
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, DiagCode::HeaderPathMismatch);
    }

    #[test]
    fn self_import_rejected() {
        let mut interner = Interner::new();
        let facts = facts(&mut interner, "module selfmod;\nuse selfmod;\n");
        let name = module_segments(&mut interner, &[], &[b"selfmod"]).unwrap();
        let (_, edges, diags) = build_module_graph(&interner, vec![(FileId(0), name, facts)]);
        assert!(edges.is_empty());
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, DiagCode::SelfImport);
    }

    #[test]
    fn cycle_of_two_reports_least_first() {
        let mut interner = Interner::new();
        let f_main = facts(&mut interner, "module main;\nuse b;\n");
        let f_b = facts(&mut interner, "module b;\nuse main;\n");
        let n_main = module_segments(&mut interner, &[], &[b"main"]).unwrap();
        let n_b = module_segments(&mut interner, &[], &[b"b"]).unwrap();
        let (_, _, diags) = build_module_graph(
            &interner,
            vec![(FileId(0), n_main, f_main), (FileId(1), n_b, f_b)],
        );
        let cycle: Vec<_> = diags
            .iter()
            .filter(|d| d.code == DiagCode::ImportCycle)
            .collect();
        assert_eq!(cycle.len(), 1);
        assert!(cycle[0].message.contains("b -> main -> b"));
    }

    #[test]
    fn cycle_of_three() {
        let mut interner = Interner::new();
        let f_main = facts(&mut interner, "module main;\nuse b;\n");
        let f_b = facts(&mut interner, "module b;\nuse c;\n");
        let f_c = facts(&mut interner, "module c;\nuse main;\n");
        let n_main = module_segments(&mut interner, &[], &[b"main"]).unwrap();
        let n_b = module_segments(&mut interner, &[], &[b"b"]).unwrap();
        let n_c = module_segments(&mut interner, &[], &[b"c"]).unwrap();
        let (_, _, diags) = build_module_graph(
            &interner,
            vec![
                (FileId(0), n_main, f_main),
                (FileId(1), n_b, f_b),
                (FileId(2), n_c, f_c),
            ],
        );
        let cycle: Vec<_> = diags
            .iter()
            .filter(|d| d.code == DiagCode::ImportCycle)
            .collect();
        assert_eq!(cycle.len(), 1);
        assert!(cycle[0].message.contains("b -> c -> main -> b"));
    }

    #[test]
    fn diamond_is_acyclic() {
        let mut interner = Interner::new();
        let f_main = facts(&mut interner, "module main;\nuse a, b;\n");
        let f_a = facts(&mut interner, "module a;\nuse d;\n");
        let f_b = facts(&mut interner, "module b;\nuse d;\n");
        let f_d = facts(&mut interner, "module d;\n");
        let n_main = module_segments(&mut interner, &[], &[b"main"]).unwrap();
        let n_a = module_segments(&mut interner, &[], &[b"a"]).unwrap();
        let n_b = module_segments(&mut interner, &[], &[b"b"]).unwrap();
        let n_d = module_segments(&mut interner, &[], &[b"d"]).unwrap();
        let (_, _, diags) = build_module_graph(
            &interner,
            vec![
                (FileId(0), n_main, f_main),
                (FileId(1), n_a, f_a),
                (FileId(2), n_b, f_b),
                (FileId(3), n_d, f_d),
            ],
        );
        assert!(diags.is_empty());
    }
}
