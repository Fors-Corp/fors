//! Integer and scalar-FP register operands.
//!
//! Register 31 is architecturally overloaded: depending on the *instruction
//! field* it sits in, encoding `11111` means either the stack pointer or the
//! zero register. The two are never interchangeable (`add sp, x0, #0` and
//! `add xzr, x0, #0` are different instructions with the same bit pattern
//! only by coincidence of `Rd`), so `Reg` carries that distinction as part of
//! its identity rather than leaving callers to remember which field they're
//! filling in — exactly the "raw u8 soup" this crate exists to avoid.

use core::fmt;

/// A general-purpose register operand: `X0`-`X30` / `W0`-`W30`, plus the
/// two aliases of encoding 31 (`SP`/`WSP` and `XZR`/`WZR`).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Reg {
    /// 0-31, architectural `Rn`/`Rd`/`Rm`/`Rt` encoding.
    num: u8,
    is64: bool,
    /// Only meaningful when `num == 31`: true = SP/WSP, false = XZR/WZR.
    is_sp: bool,
}

impl Reg {
    /// `X0`-`X30`. Panics outside 0..=30 — this is a program-construction
    /// error (a bad literal in code we wrote), not a bad input to validate;
    /// `Rn`-field-31 must go through [`Reg::sp`] or [`Reg::xzr`] to say
    /// which meaning of 31 is intended.
    pub const fn x(n: u8) -> Reg {
        assert!(
            n <= 30,
            "Reg::x(n) takes 0..=30; use Reg::sp()/Reg::xzr() for 31"
        );
        Reg {
            num: n,
            is64: true,
            is_sp: false,
        }
    }

    /// `W0`-`W30`.
    pub const fn w(n: u8) -> Reg {
        assert!(
            n <= 30,
            "Reg::w(n) takes 0..=30; use Reg::wsp()/Reg::wzr() for 31"
        );
        Reg {
            num: n,
            is64: false,
            is_sp: false,
        }
    }

    pub const fn sp() -> Reg {
        Reg {
            num: 31,
            is64: true,
            is_sp: true,
        }
    }

    pub const fn wsp() -> Reg {
        Reg {
            num: 31,
            is64: false,
            is_sp: true,
        }
    }

    pub const fn xzr() -> Reg {
        Reg {
            num: 31,
            is64: true,
            is_sp: false,
        }
    }

    pub const fn wzr() -> Reg {
        Reg {
            num: 31,
            is64: false,
            is_sp: false,
        }
    }

    pub const fn is64(self) -> bool {
        self.is64
    }

    pub const fn is_sp(self) -> bool {
        self.num == 31 && self.is_sp
    }

    pub const fn is_zr(self) -> bool {
        self.num == 31 && !self.is_sp
    }

    /// The 5-bit architectural encoding (`SP` and `XZR` both encode as 31;
    /// callers pick which one is legal for the field they're filling).
    pub const fn encoding(self) -> u32 {
        self.num as u32
    }

    /// Same register, other width (`X0.with_width(false) == W0`). Preserves
    /// the SP/ZR flavor of encoding 31.
    pub const fn with64(self, is64: bool) -> Reg {
        Reg {
            num: self.num,
            is64,
            is_sp: self.is_sp,
        }
    }
}

impl fmt::Display for Reg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.num == 31 {
            let s = match (self.is_sp, self.is64) {
                (true, true) => "sp",
                (true, false) => "wsp",
                (false, true) => "xzr",
                (false, false) => "wzr",
            };
            write!(f, "{s}")
        } else if self.is64 {
            write!(f, "x{}", self.num)
        } else {
            write!(f, "w{}", self.num)
        }
    }
}

/// Scalar floating-point register width. `V` (128-bit vector) is not needed
/// for the scalar dev backend yet and is deliberately left out; adding it
/// is a matter of another variant plus its own `size`/`type` field values,
/// not a redesign.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum FpWidth {
    S,
    D,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FpReg {
    num: u8,
    width: FpWidth,
}

impl FpReg {
    pub const fn s(n: u8) -> FpReg {
        assert!(n <= 31);
        FpReg {
            num: n,
            width: FpWidth::S,
        }
    }

    pub const fn d(n: u8) -> FpReg {
        assert!(n <= 31);
        FpReg {
            num: n,
            width: FpWidth::D,
        }
    }

    pub const fn width(self) -> FpWidth {
        self.width
    }

    pub const fn is_double(self) -> bool {
        matches!(self.width, FpWidth::D)
    }

    pub const fn encoding(self) -> u32 {
        self.num as u32
    }

    pub const fn with_width(self, width: FpWidth) -> FpReg {
        FpReg {
            num: self.num,
            width,
        }
    }
}

impl fmt::Display for FpReg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let c = match self.width {
            FpWidth::S => 's',
            FpWidth::D => 'd',
        };
        write!(f, "{c}{}", self.num)
    }
}
