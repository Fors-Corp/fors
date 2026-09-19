//! Ch08 Rule 17: the closed prelude list, present in every module scope.

pub const PRELUDE_TYPES: [&[u8]; 20] = [
    b"i8", b"i16", b"i32", b"i64", b"u8", b"u16", b"u32", b"u64", b"isize", b"usize", b"f32", b"f64", b"bool", b"Str",
    b"Slice", b"Array", b"vector", b"mask", b"atomic", b"rawptr",
];
pub const PRELUDE_TYPES2: [&[u8]; 4] = [b"Own", b"Ref", b"Arena", b"Option"];
pub const PRELUDE_TYPES3: [&[u8]; 2] = [b"Shared", b"ErrorFrom"];

pub const PRELUDE_VALUES: [&[u8]; 3] = [b"some", b"none", b"reduce"];

/// Denote `std.<name>` (ch08 Rule 17). Order matches `fors_index`'s list.
pub const PRELUDE_MODULES: [&[u8]; 8] = [b"io", b"fs", b"net", b"proc", b"time", b"rand", b"env", b"gpu"];

pub fn is_prelude_type(name: &[u8]) -> bool {
    PRELUDE_TYPES.contains(&name) || PRELUDE_TYPES2.contains(&name) || PRELUDE_TYPES3.contains(&name)
}

pub fn is_prelude_value(name: &[u8]) -> bool {
    PRELUDE_VALUES.contains(&name)
}

pub fn is_prelude_module(name: &[u8]) -> bool {
    PRELUDE_MODULES.contains(&name)
}
