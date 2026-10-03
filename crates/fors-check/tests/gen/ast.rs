//! The generator's own typed program model. A program is built bottom-up
//! from this AST, every expression carrying the type the generator derived
//! for it (the "generator's own typing"), then rendered to source text with a
//! span for every node so a mutation can name the exact site it breaks.

/// A node identity, unique within one program. The renderer records the byte
/// span of every node it prints under its id.
pub type Id = u32;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Prim {
    I8,
    I16,
    I32,
    I64,
    U8,
    U16,
    U32,
    U64,
    Usize,
    F32,
    F64,
    Bool,
}

pub const INTS: [Prim; 9] = [
    Prim::I8,
    Prim::I16,
    Prim::I32,
    Prim::I64,
    Prim::U8,
    Prim::U16,
    Prim::U32,
    Prim::U64,
    Prim::Usize,
];
pub const NUMS: [Prim; 11] = [
    Prim::I8,
    Prim::I16,
    Prim::I32,
    Prim::I64,
    Prim::U8,
    Prim::U16,
    Prim::U32,
    Prim::U64,
    Prim::Usize,
    Prim::F32,
    Prim::F64,
];

impl Prim {
    pub fn name(self) -> &'static str {
        match self {
            Prim::I8 => "i8",
            Prim::I16 => "i16",
            Prim::I32 => "i32",
            Prim::I64 => "i64",
            Prim::U8 => "u8",
            Prim::U16 => "u16",
            Prim::U32 => "u32",
            Prim::U64 => "u64",
            Prim::Usize => "usize",
            Prim::F32 => "f32",
            Prim::F64 => "f64",
            Prim::Bool => "bool",
        }
    }
    pub fn is_int(self) -> bool {
        INTS.contains(&self)
    }
    pub fn is_float(self) -> bool {
        matches!(self, Prim::F32 | Prim::F64)
    }
    pub fn is_num(self) -> bool {
        self != Prim::Bool
    }
    pub fn is_signed_int(self) -> bool {
        matches!(self, Prim::I8 | Prim::I16 | Prim::I32 | Prim::I64)
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Ty {
    Prim(Prim),
    Unit,
    /// A struct or enum by name, with its type arguments.
    Adt(String, Vec<Ty>),
    Option(Box<Ty>),
    Tuple(Vec<Ty>),
    Array(Box<Ty>, u32),
    /// A rigid generic parameter in scope.
    Param(String),
}

impl Ty {
    pub fn opt(t: Ty) -> Ty {
        Ty::Option(Box::new(t))
    }
    pub fn adt(name: &str) -> Ty {
        Ty::Adt(name.to_string(), Vec::new())
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Conv {
    Let,
    Inout,
    Sink,
}

impl Conv {
    pub fn word(self) -> &'static str {
        match self {
            Conv::Let => "let",
            Conv::Inout => "inout",
            Conv::Sink => "sink",
        }
    }
}

// ----------------------------------------------------------------- items

#[derive(Clone, Debug)]
pub struct GParam {
    pub id: Id,
    pub name: String,
    /// Bounds as written: `Copyable`, `Add`, `Tr0`.
    pub bounds: Vec<String>,
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: String,
    pub ty: Ty,
}

#[derive(Clone, Debug)]
pub struct StructDecl {
    pub id: Id,
    pub name: String,
    pub generics: Vec<GParam>,
    pub fields: Vec<Field>,
}

#[derive(Clone, Debug)]
pub enum VShape {
    Unit,
    Tuple(Vec<Ty>),
    Record(Vec<Field>),
}

#[derive(Clone, Debug)]
pub struct Variant {
    pub name: String,
    pub shape: VShape,
}

#[derive(Clone, Debug)]
pub struct EnumDecl {
    pub id: Id,
    pub name: String,
    pub generics: Vec<GParam>,
    pub variants: Vec<Variant>,
}

#[derive(Clone, Debug)]
pub struct Param {
    pub id: Id,
    pub conv: Conv,
    pub name: String,
    /// `None` is the bare receiver `let self`.
    pub ty: Option<Ty>,
    pub ty_id: Id,
}

#[derive(Clone, Debug)]
pub struct FnDecl {
    pub id: Id,
    pub name: String,
    pub name_id: Id,
    /// `fn name[..](..) -> R raises E`, without the body.
    pub sig_id: Id,
    pub attrs: Vec<String>,
    pub generics: Vec<GParam>,
    pub params: Vec<Param>,
    pub ret: Ty,
    pub ret_id: Id,
    pub raises: Option<Ty>,
    /// `None` is a required trait method (`;`).
    pub body: Option<Block>,
}

#[derive(Clone, Debug)]
pub struct TraitDecl {
    pub id: Id,
    pub name: String,
    pub methods: Vec<FnDecl>,
}

#[derive(Clone, Debug)]
pub struct ImplDecl {
    pub id: Id,
    /// `impl[..] Tr for Ty`, without the body.
    pub head_id: Id,
    pub generics: Vec<GParam>,
    pub trait_name: Option<String>,
    /// Trait arguments, as source text, e.g. `usize` in `Index[usize]`.
    pub trait_args: Vec<Ty>,
    pub self_ty: Ty,
    pub assoc: Vec<(String, Ty)>,
    pub methods: Vec<FnDecl>,
}

#[derive(Clone, Debug)]
pub struct ConstDecl {
    pub id: Id,
    pub name: String,
    pub ty: Ty,
    pub value: Expr,
}

#[derive(Clone, Debug)]
pub enum Item {
    Struct(StructDecl),
    Enum(EnumDecl),
    Trait(TraitDecl),
    Impl(ImplDecl),
    Fn(FnDecl),
    Const(ConstDecl),
    /// A declaration pasted as source text (a template injection).
    Raw {
        id: Id,
        text: String,
    },
}

impl Item {
    pub fn id(&self) -> Id {
        match self {
            Item::Struct(d) => d.id,
            Item::Enum(d) => d.id,
            Item::Trait(d) => d.id,
            Item::Impl(d) => d.id,
            Item::Fn(d) => d.id,
            Item::Const(d) => d.id,
            Item::Raw { id, .. } => *id,
        }
    }
}

// ------------------------------------------------------------ statements

#[derive(Clone, Debug)]
pub struct Block {
    pub id: Id,
    pub stmts: Vec<Stmt>,
    pub tail: Option<Box<Expr>>,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub id: Id,
    pub kind: SK,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum AssignOp {
    Set,
    Add,
    Sub,
    Mul,
}

/// A statement. The AST is test-only and every node is built once, so the
/// size of its variants is of no interest.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug)]
pub enum SK {
    Let {
        var: bool,
        name: String,
        ty: Option<Ty>,
        ty_id: Id,
        init: Option<Expr>,
    },
    Assign(Expr, AssignOp, Expr),
    Expr(Expr),
    If {
        cond: Expr,
        then: Block,
        els: Option<Block>,
    },
    Match {
        scrut: Expr,
        arms: Vec<Arm>,
    },
    For {
        var: String,
        iter: Expr,
        body: Block,
    },
    While {
        cond: Expr,
        body: Block,
    },
    Return(Option<Expr>),
    Raise(Expr),
    Defer {
        err: bool,
        body: Block,
    },
    Break,
    Continue,
    /// A statement pasted as source text.
    Raw(String),
}

#[derive(Clone, Debug)]
pub struct Arm {
    pub id: Id,
    pub pat: Pat,
    pub body: ArmBody,
}

#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug)]
pub enum ArmBody {
    Expr(Expr),
    Block(Block),
}

#[derive(Clone, Debug)]
pub struct Pat {
    pub id: Id,
    pub kind: PK,
}

#[derive(Clone, Debug)]
pub enum PSub {
    Unit,
    Tuple(Vec<Pat>),
    /// `{ name: pat, .. }`.
    Rec(Vec<(String, Pat)>),
}

#[derive(Clone, Debug)]
pub enum PK {
    Wild,
    Int(i64),
    Bool(bool),
    /// `let name`.
    Bind(String),
    /// A bare path such as a `const` name or (illegally) a fn or type name.
    Bare(String),
    Variant {
        adt: String,
        variant: String,
        dot: bool,
        sub: PSub,
    },
    Some(Box<Pat>),
    None,
}

// ----------------------------------------------------------- expressions

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnOp {
    Neg,
    Not,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    BitAnd,
    BitOr,
    BitXor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    /// `a ..< b`, used only as a `for` iterable.
    Range,
}

impl BinOp {
    pub fn text(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::Rem => "%",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",
            BinOp::Eq => "==",
            BinOp::Ne => "!=",
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            BinOp::Gt => ">",
            BinOp::Ge => ">=",
            BinOp::And => "and",
            BinOp::Or => "or",
            BinOp::Range => "..<",
        }
    }
    pub fn is_cmp(self) -> bool {
        matches!(
            self,
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge
        )
    }
    pub fn is_bit(self) -> bool {
        matches!(self, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor)
    }
    /// The operator trait this operator is resolved through (ch09 R21).
    pub fn trait_name(self) -> Option<&'static str> {
        Some(match self {
            BinOp::Add => "Add",
            BinOp::Sub => "Sub",
            BinOp::Mul => "Mul",
            BinOp::Div => "Div",
            BinOp::Rem => "Rem",
            BinOp::BitAnd => "BitAnd",
            BinOp::BitOr => "BitOr",
            BinOp::BitXor => "BitXor",
            BinOp::Eq | BinOp::Ne => "Eq",
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => "Ord",
            _ => return None,
        })
    }
}

/// A callee's declared signature, kept on the call node so a mutation can
/// read conventions and parameter types without a symbol table.
#[derive(Clone, Debug)]
pub struct Sig {
    pub generics: Vec<GParam>,
    pub params: Vec<(Conv, String, Ty)>,
    pub ret: Ty,
    pub raises: Option<Ty>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Marker {
    None,
    /// `&place`.
    Inout,
    /// `&out place`.
    Set,
}

#[derive(Clone, Debug)]
pub struct Arg {
    pub id: Id,
    pub label: Option<String>,
    pub marker: Marker,
    pub e: Expr,
}

#[derive(Clone, Debug)]
pub enum Flow {
    Plain,
    /// `call?`.
    Try,
    /// `call else |binder| { block }`.
    Handler {
        binder: String,
        block: Block,
    },
}

#[derive(Clone, Debug)]
pub struct Call {
    /// `f3`, `S0.make`, or a method name when wrapped in [`EK::Method`].
    pub callee: String,
    pub sig: Sig,
    /// Explicit type arguments (`f[i32](..)`).
    pub targs: Vec<Ty>,
    pub args: Vec<Arg>,
    pub flow: Flow,
}

#[derive(Clone, Debug)]
pub enum VPayload {
    Unit,
    Tuple(Vec<Expr>),
    Rec(Vec<(String, Expr)>),
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub id: Id,
    pub ty: Ty,
    pub kind: EK,
}

#[derive(Clone, Debug)]
pub enum EK {
    /// An integer literal; the suffix is present exactly in synth positions.
    Int(u64, Option<Prim>),
    /// A float literal as its source text; same suffix discipline.
    Float(String, Option<Prim>),
    Bool(bool),
    UnitLit,
    Local(String),
    Const(String),
    Field(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
    Call(Call),
    Method(Box<Expr>, Call),
    StructLit {
        name: String,
        targs: Vec<Ty>,
        fields: Vec<(String, Expr)>,
    },
    Variant {
        adt: String,
        variant: String,
        dot: bool,
        payload: VPayload,
    },
    Some(Box<Expr>),
    None,
    Tuple(Vec<Expr>),
    Array(Vec<Expr>),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Cast(Box<Expr>, Ty),
    Move(Box<Expr>),
    If(Box<Expr>, Box<Block>, Box<Block>),
    Match(Box<Expr>, Vec<Arm>),
    /// A fragment pasted as source text.
    Raw(String),
}

// --------------------------------------------------------------- program

#[derive(Clone, Debug)]
pub struct Program {
    pub seed: u64,
    /// Lines after `module m;` (e.g. `contracts: .proved;`).
    pub header: Vec<String>,
    pub items: Vec<Item>,
    pub next_id: Id,
}

impl Program {
    pub fn new(seed: u64) -> Program {
        Program {
            seed,
            header: Vec::new(),
            items: Vec::new(),
            next_id: 1,
        }
    }

    pub fn id(&mut self) -> Id {
        let i = self.next_id;
        self.next_id += 1;
        i
    }

    pub fn struct_decl(&self, name: &str) -> Option<&StructDecl> {
        self.items.iter().find_map(|i| match i {
            Item::Struct(s) if s.name == name => Some(s),
            _ => None,
        })
    }

    pub fn enum_decl(&self, name: &str) -> Option<&EnumDecl> {
        self.items.iter().find_map(|i| match i {
            Item::Enum(e) if e.name == name => Some(e),
            _ => None,
        })
    }

    pub fn trait_decl(&self, name: &str) -> Option<&TraitDecl> {
        self.items.iter().find_map(|i| match i {
            Item::Trait(t) if t.name == name => Some(t),
            _ => None,
        })
    }
}
