// Small in-memory instruction IR shared by both back ends:
//   - the printer (asm text -> `cc`/`as`/`ld`, rung 1)
//   - the encoder (machine-code bytes + our own object/executable writer,
//     rungs 2/3)
//
// This enum lists exactly the instruction forms rung 1's codegen emits
// (see main.rs `Codegen`). It intentionally does NOT cover the two
// hand-written runtime routines (`_rt_write_str`/`_rt_write_int`): those
// are frozen, pre-assembled machine code (see `runtime_blob.rs`) baked
// into the compiler, since their bytes never depend on the input program.

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cond {
    Lt,
    Gt,
    Le,
    Ge,
    Eq,
    Ne,
}

impl Cond {
    pub fn asm(self) -> &'static str {
        match self {
            Cond::Lt => "lt",
            Cond::Gt => "gt",
            Cond::Le => "le",
            Cond::Ge => "ge",
            Cond::Eq => "eq",
            Cond::Ne => "ne",
        }
    }
    /// AArch64 condition-code field value (as used by B.cond).
    pub fn code(self) -> u32 {
        match self {
            Cond::Eq => 0b0000,
            Cond::Ne => 0b0001,
            Cond::Ge => 0b1010,
            Cond::Lt => 0b1011,
            Cond::Gt => 0b1100,
            Cond::Le => 0b1101,
        }
    }
    /// Inverted condition (used by CSET's CSINC encoding).
    pub fn inverted_code(self) -> u32 {
        match self {
            Cond::Eq => Cond::Ne.code(),
            Cond::Ne => Cond::Eq.code(),
            Cond::Lt => Cond::Ge.code(),
            Cond::Ge => Cond::Lt.code(),
            Cond::Gt => Cond::Le.code(),
            Cond::Le => Cond::Gt.code(),
        }
    }
}

/// A register operand. Plain register numbers 0..=30; SP/XZR are
/// context-dependent (encoded differently by instruction class) and are
/// represented by the dedicated `Sp`/`Zr` variants at use sites that need
/// them (mov x29,sp / mov sp,x29 / neg).
pub type Reg = u8; // 0..=30
pub const SP: Reg = 31;

#[derive(Clone, Debug)]
pub enum Inst {
    /// MOVZ Xd, #imm16, LSL #(hw*16)
    Movz { rd: Reg, imm16: u16, hw: u8 },
    /// MOVK Xd, #imm16, LSL #(hw*16)
    Movk { rd: Reg, imm16: u16, hw: u8 },
    /// MOV Xd, Xm  (register-register; ORR alias, no SP involved)
    MovReg { rd: Reg, rm: Reg },
    /// MOV {sp,Xd}, {Xn,sp}  (ADD immediate #0 alias; used for frame ptr
    /// setup/teardown where one side is SP)
    MovSp { rd: Reg, rn: Reg },
    /// ADD/SUB Xd, Xn, Xm (register, shift 0)
    AddSubReg { sub: bool, rd: Reg, rn: Reg, rm: Reg },
    /// ADD/SUB {Xd,SP}, {Xn,SP}, #imm12  (SP-capable immediate form)
    AddSubImm { sub: bool, rd: Reg, rn: Reg, imm12: u16 },
    /// NEG Xd, Xm  (SUB Xd, XZR, Xm)
    Neg { rd: Reg, rm: Reg },
    Mul { rd: Reg, rn: Reg, rm: Reg },
    Sdiv { rd: Reg, rn: Reg, rm: Reg },
    /// MSUB Xd, Xn, Xm, Xa  (Xd = Xa - Xn*Xm)
    Msub { rd: Reg, rn: Reg, rm: Reg, ra: Reg },
    /// CMP Xn, Xm  (SUBS XZR, Xn, Xm)
    CmpReg { rn: Reg, rm: Reg },
    /// CMP Xn, #imm  (SUBS XZR, Xn, #imm)
    CmpImm { rn: Reg, imm12: u16 },
    Cset { rd: Reg, cond: Cond },
    Bcond { cond: Cond, label: String },
    B { label: String },
    Bl { func: String },
    Ret,
    /// STP Xt1, Xt2, [SP, #imm]!  (imm is a negative multiple of 8, e.g. -16)
    StpPreSp { rt1: Reg, rt2: Reg, imm: i16 },
    /// LDP Xt1, Xt2, [SP], #imm
    LdpPostSp { rt1: Reg, rt2: Reg, imm: i16 },
    /// STR/LDR Xt, [SP]  (unsigned-offset encoding, offset 0)
    StrSp0 { rt: Reg },
    LdrSp0 { rt: Reg },
    /// STUR/LDUR Xt, [X29, #-offset]  (unscaled signed imm9; `offset` is
    /// the positive displacement, i.e. actual imm9 = -offset)
    SturFp { rt: Reg, offset: i16 },
    LdurFp { rt: Reg, offset: i16 },
    /// ADRP Xd, <label>@PAGE
    AdrpLabel { rd: Reg, label: String },
    /// ADD Xd, Xn, <label>@PAGEOFF
    AddPageoff { rd: Reg, rn: Reg, label: String },
}

#[derive(Clone, Debug)]
pub enum Item {
    Inst(Inst),
    Label(String),
}

pub struct Function {
    pub name: String,
    pub is_global: bool,
    pub items: Vec<Item>,
}

// ---------------- printer back end (rung 1: text asm) ----------------

pub fn print_function(f: &Function, out: &mut String) {
    out.push_str(".text\n");
    if f.is_global {
        out.push_str(&format!(".globl _{}\n", f.name));
    }
    out.push_str(&format!("_{}:\n", f.name));
    for item in &f.items {
        print_item(item, out);
    }
}

fn print_item(item: &Item, out: &mut String) {
    match item {
        Item::Label(l) => out.push_str(&format!("{l}:\n")),
        Item::Inst(i) => print_inst(i, out),
    }
}

fn r(n: Reg) -> String {
    format!("x{n}")
}

fn print_inst(i: &Inst, out: &mut String) {
    match i {
        Inst::Movz { rd, imm16, hw } => {
            out.push_str(&format!("    movz {}, #{imm16}, lsl #{}\n", r(*rd), (*hw as u32) * 16))
        }
        Inst::Movk { rd, imm16, hw } => {
            out.push_str(&format!("    movk {}, #{imm16}, lsl #{}\n", r(*rd), (*hw as u32) * 16))
        }
        Inst::MovReg { rd, rm } => out.push_str(&format!("    mov {}, {}\n", r(*rd), r(*rm))),
        Inst::MovSp { rd, rn } => {
            let ds = if *rd == SP { "sp".to_string() } else { r(*rd) };
            let ns = if *rn == SP { "sp".to_string() } else { r(*rn) };
            out.push_str(&format!("    mov {ds}, {ns}\n"))
        }
        Inst::AddSubReg { sub, rd, rn, rm } => {
            let op = if *sub { "sub" } else { "add" };
            out.push_str(&format!("    {op} {}, {}, {}\n", r(*rd), r(*rn), r(*rm)))
        }
        Inst::AddSubImm { sub, rd, rn, imm12 } => {
            let op = if *sub { "sub" } else { "add" };
            let ds = if *rd == SP { "sp".to_string() } else { r(*rd) };
            let ns = if *rn == SP { "sp".to_string() } else { r(*rn) };
            out.push_str(&format!("    {op} {ds}, {ns}, #{imm12}\n"))
        }
        Inst::Neg { rd, rm } => out.push_str(&format!("    neg {}, {}\n", r(*rd), r(*rm))),
        Inst::Mul { rd, rn, rm } => out.push_str(&format!("    mul {}, {}, {}\n", r(*rd), r(*rn), r(*rm))),
        Inst::Sdiv { rd, rn, rm } => out.push_str(&format!("    sdiv {}, {}, {}\n", r(*rd), r(*rn), r(*rm))),
        Inst::Msub { rd, rn, rm, ra } => {
            out.push_str(&format!("    msub {}, {}, {}, {}\n", r(*rd), r(*rn), r(*rm), r(*ra)))
        }
        Inst::CmpReg { rn, rm } => out.push_str(&format!("    cmp {}, {}\n", r(*rn), r(*rm))),
        Inst::CmpImm { rn, imm12 } => out.push_str(&format!("    cmp {}, #{imm12}\n", r(*rn))),
        Inst::Cset { rd, cond } => out.push_str(&format!("    cset {}, {}\n", r(*rd), cond.asm())),
        Inst::Bcond { cond, label } => out.push_str(&format!("    b.{} {label}\n", cond.asm())),
        Inst::B { label } => out.push_str(&format!("    b {label}\n")),
        Inst::Bl { func } => out.push_str(&format!("    bl _{func}\n")),
        Inst::Ret => out.push_str("    ret\n"),
        Inst::StpPreSp { rt1, rt2, imm } => {
            out.push_str(&format!("    stp {}, {}, [sp, #{imm}]!\n", r(*rt1), r(*rt2)))
        }
        Inst::LdpPostSp { rt1, rt2, imm } => {
            out.push_str(&format!("    ldp {}, {}, [sp], #{imm}\n", r(*rt1), r(*rt2)))
        }
        Inst::StrSp0 { rt } => out.push_str(&format!("    str {}, [sp]\n", r(*rt))),
        Inst::LdrSp0 { rt } => out.push_str(&format!("    ldr {}, [sp]\n", r(*rt))),
        Inst::SturFp { rt, offset } => out.push_str(&format!("    stur {}, [x29, #-{offset}]\n", r(*rt))),
        Inst::LdurFp { rt, offset } => out.push_str(&format!("    ldur {}, [x29, #-{offset}]\n", r(*rt))),
        Inst::AdrpLabel { rd, label } => out.push_str(&format!("    adrp {}, {label}@PAGE\n", r(*rd))),
        Inst::AddPageoff { rd, rn, label } => {
            out.push_str(&format!("    add {}, {}, {label}@PAGEOFF\n", r(*rd), r(*rn)))
        }
    }
}
