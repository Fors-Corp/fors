//! The coverage table: one row for every rule of `fors_check::rules`, with
//! how many mutations targeted it and how many of those flipped the verdict
//! (a clean program accepted, its mutant rejected with the expected code at
//! the expected site). A rule no mutation reached is listed with the reason,
//! never hidden, and a rule that has neither a flipping mutation nor a named
//! reason fails the non-vacuity test.

use std::collections::BTreeSet;
use std::fmt::Write;

use fors_check::rules::{
    CH01_RULES, CH02_RULES, CH03_RULES, CH04_RULES, CH09_RULES, RuleEntry, RuleStatus,
};

use crate::mutate::catalogue;
use crate::runner::Tally;

/// `(chapter, rule)` of a rule no mutation reaches, and why. Each reason was
/// established against `crates/fors-check/src` (there is no emission site
/// for the code, or the code is raised only for a program this generator
/// cannot build). Nothing here is waived: every entry is printed with the
/// table, and the non-vacuity test fails if one of them ever starts to flip.
pub const UNREACHABLE: &[((u8, u16), &str)] = &[
    (
        (9, 3),
        "no emission site: an out-of-range scalar name is ch03 R1's D0001, never T0003 (`prelude::build` fixes the primitives)",
    ),
    (
        (9, 5),
        "no emission site: the prelude's types are fixed by construction (`prelude::build`), there is no program that redefines them",
    ),
    (
        (9, 6),
        "no reachable emission site: nominal identity is DefId equality by construction and a mix-up of two nominals is reported as T0026; the one site that writes code 6 is `lower.rs`'s MAX_LIST guard, a tuple variant with more than u16::MAX payload elements, which no generated program approaches",
    ),
    (
        (9, 8),
        "no emission site: `Self` is replaced inside an impl by construction (`lower`), there is no input that leaves it",
    ),
    (
        (9, 45),
        "no emission site: a failed qualified lookup is reported as T0042/T0043",
    ),
    (
        (9, 47),
        "no emission site: a bracket that reads as neither a type application nor an index is reported as T0011/T0029",
    ),
    (
        (9, 51),
        "no emission site: a `let` pattern's failure is reported as T0050 (R50) or T0031",
    ),
    (
        (4, 7),
        "needs std: the twelve root-capability types are std declarations, so a std-free build cannot even name one (a literal of `Stdout` is an unresolved name, N0014)",
    ),
    (
        (4, 13),
        "needs std: `fs.read_to_string` in a `comptime` block is std's `fs` module, absent from a std-free build",
    ),
];

pub struct Row {
    pub chapter: u8,
    pub rule: u16,
    pub code: Option<u16>,
    pub name: &'static str,
    pub implemented: bool,
    pub targeted: usize,
    pub flipped: usize,
    /// The distinct codes the targeting mutations expect.
    pub codes: Vec<&'static str>,
    pub reason: Option<&'static str>,
}

pub fn letter(chapter: u8) -> char {
    match chapter {
        1 => 'O',
        2 => 'F',
        3 => 'D',
        4 => 'A',
        _ => 'T',
    }
}

pub fn rows(t: &Tally) -> Vec<Row> {
    let mut out = Vec::new();
    let tables: [(u8, &[RuleEntry]); 5] = [
        (9, &CH09_RULES),
        (1, &CH01_RULES),
        (2, &CH02_RULES),
        (3, &CH03_RULES),
        (4, &CH04_RULES),
    ];
    for (chapter, table) in tables {
        for e in table {
            let c = t
                .per_rule
                .get(&(chapter, e.rule))
                .cloned()
                .unwrap_or_default();
            let mut codes: BTreeSet<&'static str> = BTreeSet::new();
            for d in catalogue() {
                if d.chapter == chapter && d.rule == e.rule {
                    codes.insert(d.code);
                }
            }
            out.push(Row {
                chapter,
                rule: e.rule,
                code: e.code,
                name: e.short_name,
                implemented: e.status == RuleStatus::Implemented,
                targeted: c.targeted,
                flipped: c.flipped,
                codes: codes.into_iter().collect(),
                reason: UNREACHABLE
                    .iter()
                    .find(|((ch, r), _)| *ch == chapter && *r == e.rule)
                    .map(|(_, why)| *why),
            });
        }
    }
    out
}

/// Why the row has no flipping mutation, when it is not a reached rule.
pub fn standing(r: &Row) -> &'static str {
    if r.flipped > 0 {
        "reached"
    } else if !r.implemented {
        "not implemented in the checker (rules.rs status)"
    } else if r.code.is_none() {
        "NoCode: the spec itself names no diagnostic"
    } else if r.reason.is_some() {
        "unreachable (reason below)"
    } else {
        "NOT REACHED, NO REASON: vacuous"
    }
}

/// The rows that break the non-vacuity gate: an implemented rule with a code
/// that no mutation flipped and nothing explains, a mutation that targeted a
/// rule and never flipped, and a named-unreachable rule that did flip.
pub fn violations(rows: &[Row]) -> Vec<String> {
    let mut v = Vec::new();
    for r in rows {
        let id = format!("ch{:02} R{} ({})", r.chapter, r.rule, r.name);
        if r.implemented && r.code.is_some() && r.flipped == 0 && r.reason.is_none() {
            v.push(format!(
                "{id}: no mutation flips the verdict and no reason is named ({} targeted)",
                r.targeted
            ));
        }
        if r.reason.is_some() && r.flipped > 0 {
            v.push(format!(
                "{id}: listed unreachable but {} mutations flipped; drop the stale reason",
                r.flipped
            ));
        }
    }
    v
}

pub fn render(rows: &[Row], t: &Tally) -> String {
    let mut s = String::new();
    let _ = writeln!(
        s,
        "coverage by rule (rules.rs), mutations targeted / flipped the verdict"
    );
    let _ = writeln!(
        s,
        "{:<5} {:<5} {:<7} {:>8} {:>8}  {:<28} name  [expected codes]",
        "chap", "rule", "code", "targeted", "flipped", "standing"
    );
    for r in rows {
        let code = r
            .code
            .map_or("-".to_string(), |c| format!("{}{c:04}", letter(r.chapter)));
        let codes = if r.codes.is_empty() {
            String::new()
        } else {
            format!("  [{}]", r.codes.join(" "))
        };
        let _ = writeln!(
            s,
            "ch{:02}  R{:<4} {:<7} {:>8} {:>8}  {:<28} {}{}",
            r.chapter,
            r.rule,
            code,
            r.targeted,
            r.flipped,
            standing(r).chars().take(28).collect::<String>(),
            r.name,
            codes
        );
        if let Some(why) = r.reason {
            let _ = writeln!(
                s,
                "                                                          reason: {why}"
            );
        }
    }
    // Rules the catalogue targets that have no row in rules.rs (ch01's flow
    // checks: O0002, O0003, O0004, O0008, O0023 ...).
    let listed: BTreeSet<(u8, u16)> = rows.iter().map(|r| (r.chapter, r.rule)).collect();
    let extra: Vec<_> = t
        .per_rule
        .iter()
        .filter(|(k, _)| !listed.contains(k))
        .collect();
    if !extra.is_empty() {
        let _ = writeln!(s, "rules targeted that have no row in rules.rs:");
        for ((ch, rule), c) in extra {
            let codes: BTreeSet<&str> = catalogue()
                .iter()
                .filter(|d| d.chapter == *ch && d.rule == *rule)
                .map(|d| d.code)
                .collect();
            let _ = writeln!(
                s,
                "ch{ch:02}  R{rule:<4} {:>8} {:>8}  [{}]",
                c.targeted,
                c.flipped,
                codes.into_iter().collect::<Vec<_>>().join(" ")
            );
        }
    }
    s
}
