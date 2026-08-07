use enum_as_inner::EnumAsInner;

use crate::asm::Op;
use crate::char::Char;
use crate::num::Sign;
use crate::source::Span;
use crate::symbol::Symbol;

// mod eval;
mod parse;

// pub use eval::*;
pub use parse::*;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AlfString {
    span: Span,
    chars: [Char; 5],
}

impl AlfString {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn chars(&self) -> [Char; 5] {
        self.chars
    }
}

#[derive(Clone, Debug, PartialEq, Eq, EnumAsInner)]
pub enum AtomicExprKind {
    Location,
    Symbol(Symbol),
    Number(u64),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AtomicExpr {
    span: Span,
    kind: AtomicExprKind,
}

impl AtomicExpr {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn kind(&self) -> &AtomicExprKind {
        &self.kind
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, EnumAsInner)]
pub enum ExprBinOp {
    /// `+`
    Add,
    /// `-`
    Sub,
    /// `*`
    Mul,
    /// `/`
    Div,
    /// `//`
    HighDiv,
    /// `:`
    Colon,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Expr {
    span: Span,
    sign: Option<Sign>,
    head: AtomicExpr,
    tail: Vec<(ExprBinOp, AtomicExpr)>,
}

impl Expr {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn sign(&self) -> Option<Sign> {
        self.sign
    }

    pub fn head(&self) -> &AtomicExpr {
        &self.head
    }

    pub fn tail(&self) -> &[(ExprBinOp, AtomicExpr)] {
        &self.tail
    }
}

#[derive(Clone, Debug, PartialEq, Eq, EnumAsInner)]
pub enum APartKind {
    Empty,
    Expr(Box<Expr>),
    FutureRef(Symbol),
    LiteralConstant(Box<WValue>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct APart {
    span: Span,
    kind: APartKind,
}

impl APart {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn kind(&self) -> &APartKind {
        &self.kind
    }
}

#[derive(Clone, Debug, PartialEq, Eq, EnumAsInner)]
pub enum IPartKind {
    Empty,
    Expr(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IPart {
    span: Span,
    kind: IPartKind,
}

impl IPart {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn kind(&self) -> &IPartKind {
        &self.kind
    }
}

#[derive(Clone, Debug, PartialEq, Eq, EnumAsInner)]
pub enum FPartKind {
    Empty,
    Expr(Box<Expr>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FPart {
    span: Span,
    kind: FPartKind,
}

impl FPart {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn kind(&self) -> &FPartKind {
        &self.kind
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WValue {
    span: Span,
    parts: Vec<(Expr, FPart)>,
}

impl WValue {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn parts(&self) -> &[(Expr, FPart)] {
        &self.parts
    }

    pub fn head(&self) -> &(Expr, FPart) {
        &self.parts[0]
    }

    pub fn tail(&self) -> &[(Expr, FPart)] {
        &self.parts[1..]
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MixOpAddress {
    op: Op,
    a_part: APart,
    i_part: IPart,
    f_part: FPart,
}

impl MixOpAddress {
    pub fn op(&self) -> Op {
        self.op
    }

    pub fn a_part(&self) -> &APart {
        &self.a_part
    }

    pub fn i_part(&self) -> &IPart {
        &self.i_part
    }

    pub fn f_part(&self) -> &FPart {
        &self.f_part
    }
}

#[derive(Clone, Debug, PartialEq, Eq, EnumAsInner)]
pub enum OpAddressKind {
    Mix(MixOpAddress),
    Equ(WValue),
    Orig(WValue),
    Con(WValue),
    End(WValue),
    Alf(AlfString),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpAddress {
    span: Span,
    kind: OpAddressKind,
}

impl OpAddress {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn kind(&self) -> &OpAddressKind {
        &self.kind
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Loc {
    span: Span,
    symbol: Symbol,
}

impl Loc {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn symbol(&self) -> Symbol {
        self.symbol
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Line {
    span: Span,
    loc: Option<Loc>,
    op_address: OpAddress,
}

impl Line {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn loc(&self) -> Option<&Loc> {
        self.loc.as_ref()
    }

    pub fn op_address(&self) -> &OpAddress {
        &self.op_address
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ast {
    lines: Vec<Line>,
}

impl Ast {
    pub fn lines(&self) -> &[Line] {
        &self.lines
    }
}
