//! Ch08 Rule 17: the closed prelude list, present in every module scope,
//! and the synthetic `std` module table a `use std.<m>;` resolves against
//! until `std` ships (owner decision 2026-09-19, round 5, D3). The prelude
//! holds NO modules: a std module is a name only where it is imported.

pub const PRELUDE_TYPES: [&[u8]; 20] = [
    b"i8", b"i16", b"i32", b"i64", b"u8", b"u16", b"u32", b"u64", b"isize", b"usize", b"f32", b"f64", b"bool", b"Str",
    b"Slice", b"Array", b"vector", b"mask", b"atomic", b"rawptr",
];
pub const PRELUDE_TYPES2: [&[u8]; 4] = [b"Own", b"Ref", b"Arena", b"Option"];
pub const PRELUDE_TYPES3: [&[u8]; 2] = [b"Shared", b"ErrorFrom"];

/// Round 4 (owner decisions 2026-09-19): the names ch09 Rules 4, 5, 21
/// and 23 make language-known.
pub const PRELUDE_TYPES4: [&[u8]; 20] = [
    b"never", b"Range", b"RangeIncl", b"Copyable", b"Eq", b"Ord", b"Add", b"Sub", b"Mul", b"Div", b"Rem", b"Neg", b"BitAnd",
    b"BitOr", b"BitXor", b"Shl", b"Shr", b"Iterator", b"Index", b"IndexMut",
];

pub const PRELUDE_VALUES: [&[u8]; 3] = [b"some", b"none", b"reduce"];

/// Ch08 Rule 17's synthetic `std` table (owner decision 2026-09-19, round
/// 5, D3): the std modules the compiler knows until `std` ships as source.
/// These are NOT prelude names — nothing here is in scope without a
/// `use std.<m>;` — they are the module names such a `use` may resolve to
/// in a build that contains no `std` source. `mem` is round 5's D5 home
/// for explicit allocators, `ffi` the home ch04's sealed-capability
/// corpus imports (`use std.ffi;`); the other eight are ch04 Rule 21's
/// root-capability homes.
pub const STD_MODULES: [&[u8]; 10] = [b"io", b"fs", b"net", b"proc", b"time", b"rand", b"env", b"gpu", b"mem", b"ffi"];

/// The list as the N0017 diagnostic prints it.
pub fn std_modules_list() -> String {
    let names: Vec<String> = STD_MODULES.iter().map(|n| String::from_utf8_lossy(n).into_owned()).collect();
    names.join(" ")
}

/// Ch10 Rule 2's additions: the std types the prelude names, all defined in
/// `std.mem` and its submodules. They close ch08 open question 1's type half
/// (`Buffer`, `Vec`, `Map` and friends were used unqualified with no import).
pub const PRELUDE_TYPES5: [&[u8]; 8] = [
    b"Allocator",
    b"AllocError",
    b"PageAllocator",
    b"Buffer",
    b"Vec",
    b"Map",
    b"String",
    b"Utf8Error",
];

pub fn is_prelude_type(name: &[u8]) -> bool {
    PRELUDE_TYPES.contains(&name)
        || PRELUDE_TYPES2.contains(&name)
        || PRELUDE_TYPES3.contains(&name)
        || PRELUDE_TYPES4.contains(&name)
        || PRELUDE_TYPES5.contains(&name)
}

pub fn is_prelude_value(name: &[u8]) -> bool {
    PRELUDE_VALUES.contains(&name)
}

/// Whether `name` is one of the std modules Rule 17's synthetic table
/// knows. Used for `use std.<m>;` resolution and for the "add `use
/// std.<m>;`" hint on an unresolved head segment (N0014); it is never a
/// scope lookup.
pub fn is_std_module(name: &[u8]) -> bool {
    STD_MODULES.contains(&name)
}
