//! Non-register operand types: condition codes, shifts, extends, and the
//! validated immediate wrappers. Each of these validates at construction
//! (`new`/the free functions below return `Result`), so an `Inst` built
//! through this crate's public API can only ever hold an in-range value —
//! `encode()` still re-checks register-width agreement between operands
//! (that can't be caught at a single operand's construction time), but
//! never needs to reject a raw immediate.

use crate::bitmask;
use crate::error::EncodeError;
use core::fmt;

/// The 16 AArch64 condition codes. `Cond::CS`/`Cond::CC` are the same bits
/// as the more mnemonic `HS`/`LO`; this type has one constructor per bit
/// pattern and always displays the spelling named here (the assembler
/// accepts both spellings for the same encoding, so this is a display
/// choice, not a coverage gap).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Cond(u8);

impl Cond {
    pub const EQ: Cond = Cond(0b0000);
    pub const NE: Cond = Cond(0b0001);
    pub const CS: Cond = Cond(0b0010);
    pub const CC: Cond = Cond(0b0011);
    pub const MI: Cond = Cond(0b0100);
    pub const PL: Cond = Cond(0b0101);
    pub const VS: Cond = Cond(0b0110);
    pub const VC: Cond = Cond(0b0111);
    pub const HI: Cond = Cond(0b1000);
    pub const LS: Cond = Cond(0b1001);
    pub const GE: Cond = Cond(0b1010);
    pub const LT: Cond = Cond(0b1011);
    pub const GT: Cond = Cond(0b1100);
    pub const LE: Cond = Cond(0b1101);
    pub const AL: Cond = Cond(0b1110);
    pub const NV: Cond = Cond(0b1111);

    pub const ALL: [Cond; 16] = [
        Cond::EQ,
        Cond::NE,
        Cond::CS,
        Cond::CC,
        Cond::MI,
        Cond::PL,
        Cond::VS,
        Cond::VC,
        Cond::HI,
        Cond::LS,
        Cond::GE,
        Cond::LT,
        Cond::GT,
        Cond::LE,
        Cond::AL,
        Cond::NV,
    ];

    pub const fn code(self) -> u32 {
        self.0 as u32
    }

    /// The complementary condition (flips the least-significant bit, per
    /// the ARM ARM's definition of `invert`). Used to build `CSET`/`CSETM`
    /// as aliases of `CSINC`/`CSINV` with `rn == rm == XZR`.
    pub const fn inverted(self) -> Cond {
        Cond(self.0 ^ 1)
    }

    pub const fn mnemonic(self) -> &'static str {
        match self.0 {
            0b0000 => "eq",
            0b0001 => "ne",
            0b0010 => "cs",
            0b0011 => "cc",
            0b0100 => "mi",
            0b0101 => "pl",
            0b0110 => "vs",
            0b0111 => "vc",
            0b1000 => "hi",
            0b1001 => "ls",
            0b1010 => "ge",
            0b1011 => "lt",
            0b1100 => "gt",
            0b1101 => "le",
            0b1110 => "al",
            _ => "nv",
        }
    }
}

impl fmt::Display for Cond {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.mnemonic())
    }
}

/// Shift kind for shifted-register data-processing instructions. `ROR` is
/// only legal on the logical (`AND`/`ORR`/`EOR`/...) family, never on
/// `ADD`/`SUB`; instruction constructors reject it there with
/// [`EncodeError::InvalidShiftForForm`] rather than silently accepting it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ShiftKind {
    Lsl,
    Lsr,
    Asr,
    Ror,
}

impl ShiftKind {
    pub(crate) const fn encoding(self) -> u32 {
        match self {
            ShiftKind::Lsl => 0b00,
            ShiftKind::Lsr => 0b01,
            ShiftKind::Asr => 0b10,
            ShiftKind::Ror => 0b11,
        }
    }

    const fn mnemonic(self) -> &'static str {
        match self {
            ShiftKind::Lsl => "lsl",
            ShiftKind::Lsr => "lsr",
            ShiftKind::Asr => "asr",
            ShiftKind::Ror => "ror",
        }
    }
}

/// A validated `<shift> #<amount>` for a shifted-register operand: `amount`
/// is checked against the operand width (0..=31 for a 32-bit register,
/// 0..=63 for 64-bit) at construction.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RegShift {
    kind: ShiftKind,
    amount: u8,
}

impl RegShift {
    pub fn new(kind: ShiftKind, amount: u8, is64: bool) -> Result<RegShift, EncodeError> {
        let max = if is64 { 63 } else { 31 };
        if amount > max {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "shifted-register amount",
                value: amount as i64,
            });
        }
        Ok(RegShift { kind, amount })
    }

    pub const fn none() -> RegShift {
        RegShift {
            kind: ShiftKind::Lsl,
            amount: 0,
        }
    }

    pub(crate) const fn kind(self) -> ShiftKind {
        self.kind
    }

    pub(crate) const fn amount(self) -> u32 {
        self.amount as u32
    }
}

impl fmt::Display for RegShift {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.amount == 0 && matches!(self.kind, ShiftKind::Lsl) {
            Ok(())
        } else {
            write!(f, ", {} #{}", self.kind.mnemonic(), self.amount)
        }
    }
}

/// Extend kind for extended-register `ADD`/`SUB` (and their `CMP`/`CMN`
/// aliases).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum ExtendKind {
    Uxtb,
    Uxth,
    Uxtw,
    Uxtx,
    Sxtb,
    Sxth,
    Sxtw,
    Sxtx,
}

impl ExtendKind {
    pub(crate) const fn encoding(self) -> u32 {
        match self {
            ExtendKind::Uxtb => 0b000,
            ExtendKind::Uxth => 0b001,
            ExtendKind::Uxtw => 0b010,
            ExtendKind::Uxtx => 0b011,
            ExtendKind::Sxtb => 0b100,
            ExtendKind::Sxth => 0b101,
            ExtendKind::Sxtw => 0b110,
            ExtendKind::Sxtx => 0b111,
        }
    }

    const fn mnemonic(self) -> &'static str {
        match self {
            ExtendKind::Uxtb => "uxtb",
            ExtendKind::Uxth => "uxth",
            ExtendKind::Uxtw => "uxtw",
            ExtendKind::Uxtx => "uxtx",
            ExtendKind::Sxtb => "sxtb",
            ExtendKind::Sxth => "sxth",
            ExtendKind::Sxtw => "sxtw",
            ExtendKind::Sxtx => "sxtx",
        }
    }
}

/// A validated `<extend> {#amount}` for an extended-register operand.
/// `amount` is architecturally restricted to 0..=4 regardless of width.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct RegExtend {
    kind: ExtendKind,
    amount: u8,
}

impl RegExtend {
    pub fn new(kind: ExtendKind, amount: u8) -> Result<RegExtend, EncodeError> {
        if amount > 4 {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "extended-register amount",
                value: amount as i64,
            });
        }
        Ok(RegExtend { kind, amount })
    }

    pub(crate) const fn kind(self) -> ExtendKind {
        self.kind
    }

    pub(crate) const fn amount(self) -> u32 {
        self.amount as u32
    }
}

impl fmt::Display for RegExtend {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ", {}", self.kind.mnemonic())?;
        if self.amount != 0 {
            write!(f, " #{}", self.amount)?;
        }
        Ok(())
    }
}

/// A 12-bit unsigned immediate for `ADD`/`SUB` (immediate) with the
/// automatic `LSL #12` selection assemblers perform: any `value` that fits
/// in 12 bits is used directly, and any value that is a multiple of 4096
/// whose top 12 bits fit is encoded shifted. Anything else is rejected at
/// construction — `encode()` can then just place the bits.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Uimm12Lsl {
    raw: u16,
    shift12: bool,
}

impl Uimm12Lsl {
    pub fn new(value: u64) -> Result<Uimm12Lsl, EncodeError> {
        if value <= 0xFFF {
            Ok(Uimm12Lsl {
                raw: value as u16,
                shift12: false,
            })
        } else if value & 0xFFF == 0 && (value >> 12) <= 0xFFF {
            Ok(Uimm12Lsl {
                raw: (value >> 12) as u16,
                shift12: true,
            })
        } else {
            Err(EncodeError::ImmediateOutOfRange {
                what: "ADD/SUB immediate",
                value: value as i64,
            })
        }
    }

    pub(crate) const fn raw(self) -> u32 {
        self.raw as u32
    }

    pub(crate) const fn shift12(self) -> bool {
        self.shift12
    }

    pub fn value(self) -> u64 {
        if self.shift12 {
            (self.raw as u64) << 12
        } else {
            self.raw as u64
        }
    }
}

impl fmt::Display for Uimm12Lsl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.shift12 {
            write!(f, "#{}, lsl #12", self.raw)
        } else {
            write!(f, "#{}", self.raw)
        }
    }
}

/// A validated AArch64 bitmask immediate (the `N:immr:imms` encoding used
/// by `AND`/`ORR`/`EOR`/`ANDS` immediate forms). See `bitmask.rs` for the
/// algorithm; this type just owns a value that has already been through it
/// successfully, plus the width it was validated at (a 64-bit `LogicalImm`
/// cannot be reused on a 32-bit instruction, since the field widths and
/// legal `N` differ).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct LogicalImm {
    n: u8,
    immr: u8,
    imms: u8,
    is64: bool,
    value: u64,
}

impl LogicalImm {
    pub fn new(value: u64, is64: bool) -> Result<LogicalImm, EncodeError> {
        let reg_size = if is64 { 64 } else { 32 };
        let target = if is64 { value } else { (value as u32) as u64 };
        match bitmask::encode_bitmask(target, reg_size) {
            Some((n, immr, imms)) => Ok(LogicalImm {
                n,
                immr,
                imms,
                is64,
                value: target,
            }),
            None => Err(EncodeError::UnencodableLogicalImmediate {
                value: target,
                is64,
            }),
        }
    }

    pub(crate) const fn n(self) -> u32 {
        self.n as u32
    }

    pub(crate) const fn immr(self) -> u32 {
        self.immr as u32
    }

    pub(crate) const fn imms(self) -> u32 {
        self.imms as u32
    }

    pub const fn is64(self) -> bool {
        self.is64
    }

    pub const fn value(self) -> u64 {
        self.value
    }
}

impl fmt::Display for LogicalImm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{:#x}", self.value)
    }
}

/// A signed, word-aligned PC-relative branch offset (bytes), validated to
/// fit `bits` bits once divided by 4. Shared by `B`/`BL` (26 bits),
/// `B.cond`/`CBZ`/`CBNZ` (19 bits) and `TBZ`/`TBNZ` (14 bits).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct BranchOffset {
    bits: u32,
    word_off: i32,
}

impl BranchOffset {
    pub fn new(bytes: i64, bits: u32, what: &'static str) -> Result<BranchOffset, EncodeError> {
        if bytes % 4 != 0 {
            return Err(EncodeError::MisalignedOffset { what, value: bytes });
        }
        let word_off = bytes / 4;
        let min = -(1i64 << (bits - 1));
        let max = (1i64 << (bits - 1)) - 1;
        if word_off < min || word_off > max {
            return Err(EncodeError::ImmediateOutOfRange { what, value: bytes });
        }
        Ok(BranchOffset {
            bits,
            word_off: word_off as i32,
        })
    }

    pub(crate) fn encoding(self) -> u32 {
        (self.word_off as u32) & ((1u32 << self.bits) - 1)
    }

    pub fn bytes(self) -> i64 {
        (self.word_off as i64) * 4
    }
}

impl fmt::Display for BranchOffset {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.bytes())
    }
}

/// A signed *byte* offset for `ADR` (21 bits, no alignment requirement —
/// `ADR` can target any byte).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AdrOffset(i32);

impl AdrOffset {
    pub fn new(bytes: i64) -> Result<AdrOffset, EncodeError> {
        if !(-(1i64 << 20)..(1i64 << 20)).contains(&bytes) {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "ADR offset",
                value: bytes,
            });
        }
        Ok(AdrOffset(bytes as i32))
    }

    pub(crate) fn encoding(self) -> (u32, u32) {
        let imm21 = (self.0 as u32) & 0x1F_FFFF;
        (imm21 & 0b11, imm21 >> 2) // (immlo, immhi)
    }

    pub fn bytes(self) -> i64 {
        self.0 as i64
    }
}

impl fmt::Display for AdrOffset {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// A signed *page count* for `ADRP` (21 bits): the caller has already
/// computed `(target_page - this_page)`, since a raw encoder has no notion
/// of link-time addresses.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct AdrpOffset(i32);

impl AdrpOffset {
    pub fn new(pages: i64) -> Result<AdrpOffset, EncodeError> {
        if !(-(1i64 << 20)..(1i64 << 20)).contains(&pages) {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "ADRP page offset",
                value: pages,
            });
        }
        Ok(AdrpOffset(pages as i32))
    }

    pub(crate) fn encoding(self) -> (u32, u32) {
        let imm21 = (self.0 as u32) & 0x1F_FFFF;
        (imm21 & 0b11, imm21 >> 2)
    }

    pub fn pages(self) -> i64 {
        self.0 as i64
    }
}

impl fmt::Display for AdrpOffset {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Confirmed empirically against clang's integrated assembler
        // (see the oracle test / crate docs): `adrp xd, #N` takes N as a
        // BYTE value that must already be a multiple of 4096, and the
        // assembler right-shifts it by 12 itself — it does not accept a
        // raw page count. `self.0` is stored in pages, so this prints the
        // byte form, e.g. pages=1 -> `#4096`.
        write!(f, "#{}", (self.0 as i64) * 4096)
    }
}

/// A signed offset for unscaled loads/stores (`LDUR`/`STUR`) and
/// pre/post-indexed addressing: 9 bits, byte-granularity regardless of
/// access size.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Simm9(i16);

impl Simm9 {
    pub fn new(bytes: i64) -> Result<Simm9, EncodeError> {
        if !(-256..256).contains(&bytes) {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "unscaled/indexed offset (simm9)",
                value: bytes,
            });
        }
        Ok(Simm9(bytes as i16))
    }

    pub(crate) fn encoding(self) -> u32 {
        (self.0 as u32) & 0x1FF
    }

    pub fn value(self) -> i64 {
        self.0 as i64
    }
}

impl fmt::Display for Simm9 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

/// An unsigned, size-scaled offset for `LDR`/`STR` unsigned-offset form:
/// the raw byte offset must be a non-negative multiple of the access size
/// and fit 12 bits once divided by it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct UScaledImm12 {
    scaled: u16,
    access_size: u32,
}

impl UScaledImm12 {
    pub fn new(bytes: i64, access_size: u32) -> Result<UScaledImm12, EncodeError> {
        if bytes < 0 || !(bytes as u64).is_multiple_of(access_size as u64) {
            return Err(EncodeError::MisalignedOffset {
                what: "LDR/STR unsigned-offset",
                value: bytes,
            });
        }
        let scaled = (bytes as u64) / (access_size as u64);
        if scaled > 0xFFF {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "LDR/STR unsigned-offset",
                value: bytes,
            });
        }
        Ok(UScaledImm12 {
            scaled: scaled as u16,
            access_size,
        })
    }

    pub(crate) const fn encoding(self) -> u32 {
        self.scaled as u32
    }

    pub fn bytes(self) -> i64 {
        (self.scaled as i64) * (self.access_size as i64)
    }
}

impl fmt::Display for UScaledImm12 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.bytes())
    }
}

/// A signed, size-scaled 7-bit offset for `LDP`/`STP`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct SImm7Scaled {
    scaled: i8,
    access_size: u32,
}

impl SImm7Scaled {
    pub fn new(bytes: i64, access_size: u32) -> Result<SImm7Scaled, EncodeError> {
        if (bytes % access_size as i64) != 0 {
            return Err(EncodeError::MisalignedOffset {
                what: "LDP/STP offset",
                value: bytes,
            });
        }
        let scaled = bytes / access_size as i64;
        if !(-64..64).contains(&scaled) {
            return Err(EncodeError::ImmediateOutOfRange {
                what: "LDP/STP offset",
                value: bytes,
            });
        }
        Ok(SImm7Scaled {
            scaled: scaled as i8,
            access_size,
        })
    }

    pub(crate) fn encoding(self) -> u32 {
        (self.scaled as u32) & 0x7F
    }

    pub fn bytes(self) -> i64 {
        (self.scaled as i64) * (self.access_size as i64)
    }
}

impl fmt::Display for SImm7Scaled {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.bytes())
    }
}
