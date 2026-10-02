//! F-mono: monomorphisation's bookkeeping — the lowering-owned type store's
//! companion tables.
//!
//! **Why a lowering-owned store** (owner decision, F-mono). Instantiating a
//! generic callee means interning types the checker never interned
//! (`Pair[i64]`'s field type after `T := i64`). The checker's `TyStore` is
//! FROZEN when `check_build` returns: its rows back every `sig_hash` the
//! freeze phase computed and every content key the query engine will cache
//! on, so growing it behind their backs would silently invalidate both. So
//! `lower_build` takes a CLONE of it ([`fors_fir::ty::TyStore`] is `Clone`
//! for exactly this caller) and interns every substituted type there. The
//! checker's store is then provably untouched —
//! [`fors_fir::ty::TyStore::digest`] is what the gate test compares before
//! and after — and the clone is sound because it starts from the same rows
//! and the same hash-cons tables: a type the checker already holds keeps its
//! original `TyId` in the clone, and only genuinely new rows are appended.
//!
//! **Why instance keys past the checker's table.** The interpreter dispatches
//! `call_direct` by [`DeclKeyId`] equality (`fors-interp::exec`: `f.decl.decl
//! == key`), so each instance needs a key of its own that no declaration
//! answers to. [`Instances`] mints them from `fir.keys.len()` upwards: the
//! checker's `DeclKeyTable` is never written (a `DeclKey` row for an instance
//! would have to encode its type arguments, which would change the encoding
//! F-mono must not change), and no minted id can collide with an interned one
//! because the table only ever grows at the checker's end of the build, which
//! has already finished.

use std::collections::VecDeque;

use fors_fir::DeclKeyId;
use fors_fir::ty::TyId;
use fors_index::ids::DefId;

/// One instantiation: a callee plus the arguments it is instantiated at, in
/// R38(a)'s order (the container's parameters, then the callee's own).
#[derive(Clone, Debug)]
pub struct Instance {
    pub callee: DefId,
    /// The arguments, as `TyId`s IN THE LOWERING-OWNED STORE.
    pub args: Vec<TyId>,
    /// The fresh declaration key this instance's FMIR carries, which is what
    /// every `call_direct` to it names.
    pub key: DeclKeyId,
    /// The instance's deterministic name: the callee's own name, `$`, and
    /// the argument row's `TyId`s. Two different builds may number the types
    /// differently; ONE build always produces the same name for the same
    /// (callee, arguments), which is what the entry lookup and the dumps
    /// need.
    pub name: String,
}

/// The instance table plus the worklist of instances still to lower.
#[derive(Debug)]
pub struct Instances {
    rows: Vec<Instance>,
    pending: VecDeque<usize>,
    next_key: u32,
}

impl Instances {
    /// `keys_len` is the checker's `DeclKeyTable::len()`: the first id this
    /// crate is free to mint.
    pub fn new(keys_len: usize) -> Instances {
        Instances {
            rows: Vec::new(),
            pending: VecDeque::new(),
            next_key: keys_len as u32,
        }
    }

    /// The instance for `(callee, args)`, creating and enqueuing it the first
    /// time it is asked for. The cache is the whole of "lower the body once
    /// per distinct (callee, args)".
    pub fn request(&mut self, callee: DefId, args: &[TyId], base_name: &str) -> DeclKeyId {
        if let Some(row) = self
            .rows
            .iter()
            .find(|r| r.callee == callee && r.args == args)
        {
            return row.key;
        }
        let key = DeclKeyId(self.next_key);
        self.next_key += 1;
        let mut name = String::from(base_name);
        name.push('$');
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                name.push('_');
            }
            name.push_str(&a.0.to_string());
        }
        self.rows.push(Instance {
            callee,
            args: args.to_vec(),
            key,
            name,
        });
        self.pending.push_back(self.rows.len() - 1);
        key
    }

    /// The next instance whose body has not been lowered, in request order
    /// (which makes the lowered program's function order deterministic).
    pub fn pop_pending(&mut self) -> Option<Instance> {
        let i = self.pending.pop_front()?;
        Some(self.rows[i].clone())
    }

    pub fn len(&self) -> usize {
        self.rows.len()
    }

    pub fn is_empty(&self) -> bool {
        self.rows.is_empty()
    }
}
