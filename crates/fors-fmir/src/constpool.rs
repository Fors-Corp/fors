//! `ConstPool`: "comptime-known values, content-addressed" (design §3.1).
//! F0 has no comptime engine yet (F9's job); this pool only needs to hold
//! what `const_int`/`const_float`/`const_bool`/`const_unit`/`const_str` can
//! reference and to dedupe equal values (`intern`), standing in for the real
//! content-addressed memo of design §6 without implementing its budget
//! machinery. [decision: a plain interned `Vec<ConstValue>`, not the
//! `blake3(target_hash ‖ ...)`-keyed memo of §6 — that memo needs `Target`
//! and a comptime `Env` neither of which exist before F9]

use fors_index::interner::Symbol;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ConstValue {
    Int(i64),
    /// IEEE-754 bit pattern, never a host `f64` compare (design §5.6: no
    /// float value in this crate is ever compared by `==`).
    FloatBits(u64),
    Bool(bool),
    Unit,
    Str(Symbol),
}

use crate::ids::FmirConstId;

#[derive(Clone, Debug, Default)]
pub struct ConstPool {
    rows: Vec<ConstValue>,
}

impl ConstPool {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }

    pub fn intern(&mut self, v: ConstValue) -> FmirConstId {
        if let Some(i) = self.rows.iter().position(|r| *r == v) {
            return FmirConstId(i as u32);
        }
        let id = FmirConstId(self.rows.len() as u32);
        self.rows.push(v);
        id
    }

    pub fn row(&self, id: FmirConstId) -> ConstValue {
        self.rows[id.index()]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_values_intern_to_the_same_id() {
        let mut pool = ConstPool::new();
        let a = pool.intern(ConstValue::Int(7));
        let b = pool.intern(ConstValue::Int(7));
        let c = pool.intern(ConstValue::Int(8));
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_eq!(pool.len(), 2);
    }
}
