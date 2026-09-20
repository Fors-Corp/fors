//! The use tape (design §7.9): the ordered record of what a body does with
//! each place, emitted by typing and consumed by the flow pass (I8).
//!
//! Typing never decides an ownership question; it only writes down, in
//! source order, every value use it saw and why. [`Cause::ImplicitReceiver`]
//! carries its three fields unconditionally because ch09 R46's mandatory
//! diagnostic is built from them ("`x` was moved by the call `x.finish()`
//! at L:C, because `Builder.finish` takes `sink self` (declared at L:C)"),
//! and a later pass cannot recover them from the CST alone.

use fors_index::Symbol;
use fors_index::ids::DefId;

/// What one event did to its place.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UseKind {
    Read,
    Copy,
    Move,
    MutBorrow,
    OutBorrow,
    Assign,
    Declare,
}

/// Why the event happened — the half of an ownership diagnostic that points
/// at the *reason* rather than at the place.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Cause {
    /// A use written as itself (an operand, a `move e`, a `consume`).
    Explicit(u32),
    Argument {
        call: u32,
        param: u16,
    },
    Iterable(u32),
    Capture(u32),
    /// R46: a `sink self` method called in receiver form moved the place.
    /// All three fields are required: the call node, the method and its
    /// owner (impl or trait).
    ImplicitReceiver {
        call: u32,
        method: DefId,
        owner: DefId,
    },
}

/// One step of a place path (design §7.9: `PlaceId` interns
/// `(root local node, [Field | Index])`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Seg {
    Field(Symbol),
    Index,
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct PlaceId(pub u32);

#[derive(Clone, Copy, Debug)]
pub struct UseEvent {
    pub node: u32,
    pub place: PlaceId,
    pub kind: UseKind,
    pub cause: Cause,
}

/// One body's tape. Struct-of-arrays for the place table; the event list is
/// the only per-body heap growth typing does, and it is appended to, never
/// searched, in the hot path.
#[derive(Default)]
pub struct UseTape {
    pub events: Vec<UseEvent>,
    root: Vec<u32>,
    start: Vec<u32>,
    len: Vec<u16>,
    segs: Vec<Seg>,
}

impl UseTape {
    pub fn new() -> UseTape {
        UseTape::default()
    }

    /// The `PlaceId` for `root.path`, interning it on first sight. A body
    /// names a handful of places, so the scan is over a handful of rows and
    /// no hash table is allocated.
    pub fn intern(&mut self, root: u32, path: &[Seg]) -> PlaceId {
        for i in 0..self.root.len() {
            if self.root[i] != root || self.len[i] as usize != path.len() {
                continue;
            }
            let a = self.start[i] as usize;
            if self.segs[a..a + path.len()] == *path {
                return PlaceId(i as u32);
            }
        }
        let id = PlaceId(self.root.len() as u32);
        self.root.push(root);
        self.start.push(self.segs.len() as u32);
        self.len.push(u16::try_from(path.len()).unwrap_or(u16::MAX));
        self.segs.extend_from_slice(path);
        id
    }

    pub fn push(&mut self, node: u32, place: PlaceId, kind: UseKind, cause: Cause) {
        self.events.push(UseEvent {
            node,
            place,
            kind,
            cause,
        });
    }

    /// The root node and path of a place.
    pub fn place(&self, p: PlaceId) -> (u32, &[Seg]) {
        let i = p.0 as usize;
        let a = self.start[i] as usize;
        (self.root[i], &self.segs[a..a + self.len[i] as usize])
    }

    pub fn places(&self) -> usize {
        self.root.len()
    }

    pub fn len(&self) -> usize {
        self.events.len()
    }

    pub fn is_empty(&self) -> bool {
        self.events.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn equal_paths_intern_to_one_place() {
        let mut t = UseTape::new();
        let a = t.intern(7, &[Seg::Field(Symbol(1))]);
        let b = t.intern(7, &[Seg::Field(Symbol(1))]);
        let c = t.intern(7, &[Seg::Field(Symbol(2))]);
        let d = t.intern(8, &[Seg::Field(Symbol(1))]);
        assert_eq!(a, b);
        assert_ne!(a, c);
        assert_ne!(a, d);
        assert_eq!(t.place(a), (7, &[Seg::Field(Symbol(1))][..]));
        assert_eq!(t.places(), 3);
    }
}
