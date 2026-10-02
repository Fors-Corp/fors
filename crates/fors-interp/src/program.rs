//! The interpreter's program input (design §5.1, §7.2).
//!
//! The interpreter is the oracle: FMIR is its SOLE program input (ch05 R3).
//! A [`Program`] is a closed set of lowered declarations plus the side
//! tables lowering produced alongside them:
//! - `strings`: the bytes of every `const_str` literal, keyed by
//!   `(function index, FmirConstId)`. `ConstValue::Str` carries a `Symbol`
//!   whose bytes live in the caller's interner; copying the bytes here keeps
//!   the interpreter a pure function of (FMIR, declared inputs, capability
//!   responses) with no interner in the loop.
//! - `intrinsics`: the closed host-effect table, keyed by the raw
//!   `Symbol.0` of each `Callee::Intrinsic`. Dispatch compares the resolved
//!   NAME, never the id, so records stay deterministic across processes.
//!
//! [`Config`] carries the explicit [`Target`](design §5.1): pointer width
//! and endianness. There is deliberately no optimisation-level input
//! (design §3.6, ch02 R10): `interp_has_no_opt_level_input` constructs a
//! `Config` exhaustively, so adding an `-O`-shaped field is a compile
//! error in that test.

use fors_fmir::decl::DeclFmir;

/// v0.1's only targets are little-endian 64-bit (design §5.1).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Endian {
    Little,
}

/// The explicit target (design §5.1). The crates use Rust's own word size
/// for host bookkeeping (pool indices) and NEVER for a program-visible
/// value; `ptr_bits` is what `Isize`/`Usize` lower against.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Config {
    /// Target pointer width in bits. 64 in v0.1.
    pub ptr_bits: u8,
    /// Target endianness. Little in v0.1.
    pub endian: Endian,
}

impl Config {
    /// The v0.1 target: 64-bit little-endian.
    pub fn v0_1() -> Config {
        Config {
            ptr_bits: 64,
            endian: Endian::Little,
        }
    }
}

/// One lowered function in the program.
#[derive(Clone, Debug)]
pub struct ProgFn {
    /// The function's item name (for diagnostics and the entry lookup).
    pub name: String,
    /// The function's FMIR body.
    pub decl: DeclFmir,
    /// `(FmirConstId.0, bytes)` for every `const_str` in `decl`.
    pub strings: Vec<(u32, Vec<u8>)>,
    /// `(Symbol.0, name)` for every intrinsic `decl` names.
    pub intrinsics: Vec<(u32, String)>,
}

/// A closed, runnable program: FMIR plus its side tables.
#[derive(Clone, Debug)]
pub struct Program {
    pub fns: Vec<ProgFn>,
    /// Index into `fns` of the entry point.
    pub entry: usize,
    pub config: Config,
    /// F3: the static type names ch02 R17's `render` reads, written by
    /// lowering (`LoweredBuild::names`). Empty renders every nominal type
    /// as `..`.
    pub names: fors_fmir::names::TypeNames,
}

impl Program {
    /// The function implementing `main`, by name.
    pub fn entry_by_name(fns: Vec<ProgFn>, name: &str, config: Config) -> Option<Program> {
        let entry = fns.iter().position(|f| f.name == name)?;
        Some(Program {
            fns,
            entry,
            config,
            names: fors_fmir::names::TypeNames::default(),
        })
    }

    /// The same program with lowering's render table attached (F3).
    pub fn with_names(mut self, names: fors_fmir::names::TypeNames) -> Program {
        self.names = names;
        self
    }
}
