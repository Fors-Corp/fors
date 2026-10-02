//! The F6 memory model: allocation objects (design §5.1), arenas, brands and
//! generation checks (design §3.7, ch01 R15-R18), and the provenance table a
//! pointer [`Slot`](crate::value::Slot) names.
//!
//! Host-word-size discipline (design §5.1): every program-visible width here
//! is a fixed-width integer. `usize` appears only for host bookkeeping
//! (indexing this crate's own `Vec`s), never for a value a program can read —
//! same rule `value.rs`/`arith.rs` are grepped for.

use fors_fmir::ids::SiteId;
use fors_fmir::op::TrapKind;

/// An allocator's identity. ch01 R18: "`Own[T, A]` MUST record its producing
/// allocator's brand `A`; `deinit` with an allocator whose brand differs from
/// `A` MUST be a compile error" — the *typed* case is the checker's; the
/// ERASED case is this interpreter's `ub: allocator-mismatch` (design §5.2).
/// The brand IS the identity, so this is an FMIR `BrandId` carried across.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AllocatorId(pub u32);

impl AllocatorId {
    /// The ambient allocator: a block in no `with allocator` scope, i.e. a
    /// scope whose `brand` is `BrandId::NONE`.
    pub const AMBIENT: AllocatorId = AllocatorId(fors_fmir::ids::ABSENT);
}

/// One arena's identity (index into the machine's arena table).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ArenaId(pub u32);

/// One allocation object's identity (index into the machine's `Vec<Alloc>`).
/// Index 0 is reserved: [`PROV_NONE`] makes it unreachable.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AllocId(pub u32);

/// design §5.1's `AllocKind`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AllocKind {
    Stack,
    Heap(AllocatorId),
    Arena(ArenaId),
    Static,
    Capability,
}

/// design §5.1's `AllocState`. `Reset` is an arena's `arena_reset`/region
/// exit; ch01 R17 makes a use through it a program TRAP (`arena-generation`),
/// while `Freed` is the heap case and a `ub:` report (design §5.2).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AllocState {
    Live,
    Freed(SiteId),
    Reset(SiteId),
}

/// One bit per byte: design §5.1's `init: BitVec` — "uninit reads are
/// DETECTED". Hand-rolled because this workspace takes no dependencies.
#[derive(Clone, PartialEq, Eq, Debug, Default)]
pub struct BitVec {
    words: Vec<u64>,
    len: u32,
}

impl BitVec {
    pub fn zeros(len: u32) -> BitVec {
        BitVec {
            words: vec![0u64; (len as u64).div_ceil(64) as usize],
            len,
        }
    }

    pub fn len(&self) -> u32 {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn grow_to(&mut self, len: u32) {
        if len > self.len {
            self.len = len;
            self.words.resize((len as u64).div_ceil(64) as usize, 0);
        }
    }

    pub fn get(&self, i: u32) -> bool {
        if i >= self.len {
            return false;
        }
        let (w, b) = ((i / 64) as usize, i % 64);
        self.words[w] >> b & 1 == 1
    }

    pub fn set_range(&mut self, start: u32, len: u32, value: bool) {
        for i in start..start.saturating_add(len) {
            if i >= self.len {
                break;
            }
            let (w, b) = ((i / 64) as usize, i % 64);
            if value {
                self.words[w] |= 1u64 << b;
            } else {
                self.words[w] &= !(1u64 << b);
            }
        }
    }

    /// Is every byte of `start..start+len` initialised?
    pub fn all_set(&self, start: u32, len: u32) -> bool {
        (start..start.saturating_add(len)).all(|i| self.get(i))
    }
}

/// design §5.1's `Alloc`, field for field. `prov` records the provenance
/// stored AT pointer-sized offsets, so a pointer written into memory and read
/// back keeps its provenance instead of decaying to an integer.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Alloc {
    pub bytes: Vec<u8>,
    pub init: BitVec,
    pub prov: std::collections::BTreeMap<u32, u32>,
    pub kind: AllocKind,
    /// The arena generation this allocation was created at (0 for non-arena
    /// kinds).
    pub generation: u32,
    pub state: AllocState,
    pub align: u32,
}

impl Alloc {
    pub fn new(size: u32, align: u32, kind: AllocKind, generation: u32) -> Alloc {
        Alloc {
            bytes: vec![0u8; size as usize],
            init: BitVec::zeros(size),
            prov: std::collections::BTreeMap::new(),
            kind,
            generation,
            state: AllocState::Live,
            align,
        }
    }

    pub fn size(&self) -> u32 {
        self.bytes.len() as u32
    }

    /// Grows the object to at least `size` bytes, leaving the new bytes
    /// UNINITIALISED. An arena bump-allocates into one object, and ch01 says
    /// nothing about arena exhaustion (there is no `arena-exhausted` trap in
    /// ch02 R15's closed eight), so the backing object grows rather than
    /// inventing a ninth trap kind.
    pub fn grow_to(&mut self, size: u32) {
        if size > self.size() {
            self.bytes.resize(size as usize, 0);
            self.init.grow_to(size);
        }
    }

    /// Forgets every byte and every stored provenance: `arena_reset`'s effect
    /// on the backing object. The generation bump is what makes a surviving
    /// `Ref` trap; this is what makes a read through a *fresh* `Ref` into the
    /// same bytes a detected `ub: uninit-read` instead of a stale value.
    pub fn forget(&mut self) {
        self.init.set_range(0, self.init.len(), false);
        self.prov.clear();
        self.bytes.fill(0);
    }
}

/// design §3.7's `ArenaVal`. It lives in the machine's arena table, NOT in a
/// `Slot`: ch01 R15a gives an arena value no constructor and at most one live
/// instance per brand per block, and the generation an arena is CURRENTLY at
/// must be readable after a `reset` through a handle minted before it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ArenaVal {
    pub id: ArenaId,
    pub generation: u32,
    pub bump: u64,
    pub cap: u64,
    pub data: AllocId,
}

impl ArenaVal {
    pub fn new(id: ArenaId, data: AllocId, cap: u64) -> ArenaVal {
        ArenaVal {
            id,
            generation: 0,
            bump: 0,
            cap,
            data,
        }
    }

    /// ch01 R17's `reset`: "Every arena MUST carry a generation counter
    /// bumped on `reset`". The bump goes through [`next_generation`], so a
    /// counter at `u32::MAX` TRAPS rather than wrapping ([HOLE-2], E9).
    pub fn reset(&mut self) -> Result<(), TrapKind> {
        self.generation = next_generation(self.generation)?;
        self.bump = 0;
        Ok(())
    }
}

/// The ONE place the arena generation counter advances — design §3.7 and
/// engineering call E9 / **[HOLE-2]**: "`arena_reset` bumps `generation` (wrapping
/// is a verifier-rejected condition: `generation == u32::MAX` traps
/// `arena-generation` preemptively rather than aliasing an old generation —
/// ch01 R17 does not say what a wrapped counter does)".
///
/// A wrapped counter would silently revalidate a stale `Ref`, which is the
/// exact bug R17 exists to prevent, so the wrap is DETECTED and is never a
/// silent reuse. `arena_gen_wraps_safely` is this function's gate test.
pub fn next_generation(generation: u32) -> Result<u32, TrapKind> {
    if generation == u32::MAX {
        return Err(TrapKind::ArenaGeneration);
    }
    Ok(generation + 1)
}

/// design §3.7's `RefVal` — `{ arena, generation, off }`, 12 bytes. It is carried
/// in a [`Slot`](crate::value::Slot) as `prov` (naming the arena, via a
/// [`ProvRow`]) plus `bits` packing `(generation, off)`, which is exactly 12 bytes
/// of content inside the 16-byte slot design §5.1 fixes.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RefVal {
    pub arena: ArenaId,
    pub generation: u32,
    pub off: u32,
}

impl RefVal {
    /// The `(generation, off)` half, as a `Slot.bits` pattern.
    pub const fn pack(generation: u32, off: u32) -> u64 {
        ((generation as u64) << 32) | (off as u64)
    }

    pub const fn unpack(bits: u64) -> (u32, u32) {
        ((bits >> 32) as u32, bits as u32)
    }
}

/// What a pointer points INTO. A local slot is a target in its own right:
/// `&x` on a `let` binding does not allocate, but it still has provenance and
/// a borrow stack (design §5.2's aliasing row).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum MemTarget {
    Alloc(AllocId),
    /// A frame-local root slot (`PlaceRow.root`). `serial` is the frame's
    /// activation number: a frame INDEX is reused by the next call after a
    /// return, so a pointer that outlives its frame must be told apart from
    /// one into the frame now at that index. A mismatch is design §5.2's
    /// "use of a freed allocation" on a stack slot (`AllocKind::Stack`),
    /// reported `ub: use-after-free` — never a silent read of another
    /// frame's local and never a panic.
    Root {
        frame: u32,
        serial: u32,
        root: u32,
    },
    /// An arena `Ref`: `data` is the arena's backing object, and the slot's
    /// `bits` carry the `(generation, off)` the generation check compares.
    Arena {
        arena: ArenaId,
        data: AllocId,
    },
}

/// One provenance row: what a pointer points into, and its borrow tag
/// (design §5.1's `prov: ProvId`; in a Stacked-Borrows-shaped model the tag
/// IS the provenance, so the two live in one row rather than two slot
/// fields).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct ProvRow {
    pub target: MemTarget,
    pub tag: u32,
}

/// `Slot.prov == PROV_NONE` means "not a pointer" (design §5.1: "NONE for
/// non-pointers"). Row 0 of the provenance table is therefore a placeholder
/// no pointer ever names.
pub const PROV_NONE: u32 = 0;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generation_wrap_is_detected_never_reused() {
        // [HOLE-2] / E9: at `u32::MAX` the counter traps instead of wrapping
        // to a generation a stale `Ref` still carries.
        assert_eq!(next_generation(0), Ok(1));
        assert_eq!(next_generation(u32::MAX - 1), Ok(u32::MAX));
        assert_eq!(
            next_generation(u32::MAX),
            Err(TrapKind::ArenaGeneration),
            "a wrapped generation would silently revalidate a stale Ref"
        );
    }

    #[test]
    fn arena_reset_bumps_then_traps_at_the_ceiling() {
        let mut a = ArenaVal::new(ArenaId(0), AllocId(1), 64);
        a.bump = 32;
        assert_eq!(a.reset(), Ok(()));
        assert_eq!((a.generation, a.bump), (1, 0));
        a.generation = u32::MAX;
        assert_eq!(a.reset(), Err(TrapKind::ArenaGeneration));
        assert_eq!(
            a.generation,
            u32::MAX,
            "a trapping reset leaves the counter alone"
        );
    }

    #[test]
    fn ref_val_packing_round_trips() {
        for (g, o) in [(0u32, 0u32), (1, 8), (u32::MAX, u32::MAX)] {
            assert_eq!(RefVal::unpack(RefVal::pack(g, o)), (g, o));
        }
    }

    #[test]
    fn init_bitmap_tracks_byte_granular_initialisation() {
        let mut a = Alloc::new(16, 8, AllocKind::Heap(AllocatorId::AMBIENT), 0);
        assert!(!a.init.all_set(0, 1));
        a.init.set_range(4, 4, true);
        assert!(a.init.all_set(4, 4));
        assert!(!a.init.all_set(3, 4));
        a.forget();
        assert!(!a.init.all_set(4, 4));
    }

    #[test]
    fn growing_leaves_the_new_bytes_uninitialised() {
        let mut a = Alloc::new(4, 4, AllocKind::Arena(ArenaId(0)), 0);
        a.init.set_range(0, 4, true);
        a.grow_to(12);
        assert_eq!(a.size(), 12);
        assert!(a.init.all_set(0, 4));
        assert!(!a.init.all_set(4, 1));
    }
}
