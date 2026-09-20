//! `SitePool`: `SiteId -> (span, decl)` (design §3.1's side table; §10.3
//! budgets it at "≤ 8 B per trap site"). F0 has no real source spans yet (no
//! `fors-lower`), so `SiteRow` carries a synthetic `(line, col)` pair; the
//! textual dump/parser round-trip these exactly like any other field, and
//! real lowering will populate genuine spans without changing the shape.
//! [decision: `(line, col)` rather than a byte-offset `span: Range<u32>`,
//! since design §7.2a's trap line format is `<file>:<L>:<C>` — carrying
//! line/col directly avoids re-deriving it from a byte offset before F0 has
//! a `fors-lex` `Tokens` table to derive it from]

use crate::ids::SiteId;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SiteRow {
    pub line: u32,
    pub col: u32,
}

#[derive(Clone, Debug, Default)]
pub struct SitePool {
    rows: Vec<SiteRow>,
}

impl SitePool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn push(&mut self, row: SiteRow) -> SiteId {
        let i = self.rows.len() as u32;
        self.rows.push(row);
        SiteId(i)
    }

    pub fn row(&self, id: SiteId) -> SiteRow {
        self.rows[id.index()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn push_then_row_round_trips() {
        let mut pool = SitePool::new();
        let id = pool.push(SiteRow { line: 12, col: 3 });
        assert_eq!(pool.row(id), SiteRow { line: 12, col: 3 });
    }
}
