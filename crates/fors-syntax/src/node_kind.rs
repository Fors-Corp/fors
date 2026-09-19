//! `NodeKind`: the productions of chapter 07 that show up in the tree, plus
//! `Error` for recovered garbage. Fieldless, `#[repr(u8)]`, stored in a
//! parallel column (see [`crate::tree::Tree`]) — never boxed.
//!
//! A node exists only where it carries information: an expression level
//! with no operator at that point adds no node (`1` is one `Literal`, not a
//! ladder of ten wrappers), and a type without qualifiers is just its core.
//! Each kind below lists its children in order; everything else in the
//! node's range (keywords, operators, names, delimiters) is a token the
//! node owns directly.

#[repr(u8)]
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
pub enum NodeKind {
    /// Header clauses, `UseDecl`s, then one node per top-level declaration.
    File,
    ModuleHdr,
    ContractsClause,
    NeedsClause,
    /// `"inputs" "{" STRING { "," STRING } [ "," ] "}" ";"`, after `needs`
    /// and before `use` (ch07 grammar).
    InputsClause,
    UseDecl,
    /// `ident { "." ident }` outside expressions and types. Leaf.
    Path,
    DotLit,

    Attribute,
    AttrArg,
    // Declarations own their leading `Attribute`s and `pub` (and `soa`).
    FnDecl,
    ExternFnDecl,
    /// `[Generics] Params [ret type] [Raises] {Contract}`.
    FnSig,
    Generics,
    GParam,
    Params,
    Param,
    /// `raises` + type (in `FnSig` and `FnType`).
    Raises,
    /// `pre`/`post`/`invariant` + expression (also a struct's `invariant`).
    Contract,
    StructDecl,
    Field,
    EnumDecl,
    EVariant,
    TraitDecl,
    TraitItem,
    ImplDecl,
    ConstDecl,

    Block,
    LetStmt,
    /// `ident` or `_`. Leaf.
    Binding,
    TupleBinding,
    AssignStmt,
    ExprStmt,
    ForStmt,
    WhileStmt,
    BreakStmt,
    ContinueStmt,
    ReturnStmt,
    RaiseStmt,
    WithStmt,
    ParallelStmt,
    ParallelForStmt,
    SimdForStmt,
    SpawnStmt,
    ConsumeStmt,
    DiscardStmt,
    AttrBlockStmt,

    // ---- expressions. The n-ary kinds are flat, as in the EBNF: operands
    // are the children, the operator tokens sit between them. ----
    OrExpr,
    AndExpr,
    NotExpr,
    CmpExpr,
    BitExpr,
    RangeExpr,
    AddExpr,
    MulExpr,
    /// Operand, then one type per `as`.
    CastExpr,
    UnaryExpr,

    // Postfix forms: the first child is the operand they apply to.
    CallExpr,
    Handler,
    Bracket,
    FieldExpr,
    TryExpr,
    /// `label ":"` + argument value.
    NamedArg,
    /// `&` + place.
    InoutArg,
    /// `&out` + place.
    SetArg,
    BareOp,

    Literal,
    /// A `path` in expression position (rule 13: greedy `.ident`). Leaf.
    NameExpr,
    /// `NameExpr` or `Bracket(NameExpr, ..)`, then `FInit`s.
    StructLit,
    FInit,
    TupleOrParen,
    ArrayLit,
    /// `"asm" "(" IDENT ")" "{" AsmItem { "," AsmItem } [ "," ] "}"` (ch07
    /// grammar / R2-4). The architecture `IDENT` is a token the node owns
    /// directly; children are the `AsmItem`s.
    AsmExpr,
    /// One `in "(" IDENT ")" "=" expr`, `out "(" IDENT ")"`,
    /// `clobber "(" IDENT { "," IDENT } ")"`, or a bare `STRING`. The
    /// `expr` (for `in`) is the item's only child; the rest are tokens the
    /// node owns directly.
    AsmItem,
    Closure,
    CParam,
    /// Flat `else if` chain: `cond Block { cond Block } [ Block ]`, so a
    /// long chain does not deepen the tree.
    IfExpr,
    MatchExpr,
    Arm,
    ComptimeBlock,

    PatWild,
    /// `[-] number`, string, `true`, `false`. Leaf.
    PatLit,
    /// `path [Payload]`.
    PatPath,
    /// `"." ident [Payload]`.
    PatDot,
    PatTuple,
    Payload,
    FPat,

    /// One or more qualifiers + a type core.
    QualType,
    /// `scoped "(" ident ")"` + type (return types only).
    ScopedType,
    /// `path [ "[" targs "]" ]`; a targ is a type node or a const
    /// expression node. A bare-path targ stays a `TypeApp` leaf for the
    /// checker to classify (rule 11).
    TypeApp,
    TupleType,
    FnType,
    FParam,
    DynType,

    /// Recovered garbage: a run of skipped tokens, or a construct that
    /// could not be parsed. Always paired with a diagnostic.
    Error,

    // ---- appended, owner decision 2026-09-19 round 3 (D1/D2): additive
    // only, never reorder or remove anything above. ----
    /// `path [ "as" ident ]`, one comma-separated item of a `UseDecl`
    /// (ch07 grammar `use_item`). The `path` is the only child; the
    /// optional `"as"` and its identifier are tokens the node owns
    /// directly.
    UseItem,
    /// `"let" ident` as a `pattern` alternative (ch07 grammar, D1). Both
    /// tokens are owned directly; leaf.
    PatLet,

    // ---- appended, owner decision 2026-09-19 round 4 (associated
    // types): additive only. ----
    /// `"type" ident [ ":" bounds ] ";"` in a `TraitDecl` body (ch07
    /// `assoc_type_decl`). Children: the bound types.
    AssocTypeDecl,
    /// `"type" ident "=" type ";"` in an `ImplDecl` body (ch07
    /// `assoc_type_def`). Child: the right-hand-side type.
    AssocTypeDef,
    /// `ident "." ident ":" bounds` in a `Generics` list (ch07
    /// `gconstraint`). Introduces no name; both identifiers are tokens
    /// the node owns directly; children: the bound types.
    GConstraint,
}

impl NodeKind {
    /// Kinds that are direct children of `File` (or of an `impl`/`trait`
    /// body) and form the unit of incremental re-checking.
    pub fn is_decl(self) -> bool {
        matches!(
            self,
            NodeKind::FnDecl
                | NodeKind::ExternFnDecl
                | NodeKind::StructDecl
                | NodeKind::EnumDecl
                | NodeKind::TraitDecl
                | NodeKind::ImplDecl
                | NodeKind::ConstDecl
        )
    }
}
