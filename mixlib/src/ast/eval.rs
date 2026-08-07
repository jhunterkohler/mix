use std::error::Error;
use std::fmt;

use crate::num::{Byte, LocationCounter, Word};

use super::*;

/// Enum describing the kind of error that occurred during evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum EvalErrorKind {
    /// A literal number was out of range of [`Word`].
    NumberOutOfRange {
        /// The number's value.
        number: u64,
    },
    /// A references symbol was undefined.
    UndefinedSymbol {
        /// The undefined symbol.
        symbol: Symbol,
    },
    /// A field in a W-expression was an invalid for words.
    FieldOutOfRange {
        /// The evaluated field.
        value: Word,
    },
}

/// An error that arises during evaluation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvalError {
    span: Span,
    kind: EvalErrorKind,
}

impl EvalError {
    pub fn span(&self) -> Span {
        self.span
    }

    pub fn kind(&self) -> &EvalErrorKind {
        &self.kind
    }
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str(match self.kind {
            EvalErrorKind::NumberOutOfRange { .. } => "number out of range",
            EvalErrorKind::UndefinedSymbol { .. } => "undefined symbol",
            EvalErrorKind::FieldOutOfRange { .. } => "field out of range",
        })
    }
}

impl Error for EvalError {}

pub trait Eval {
    fn eval<F: FnMut(Symbol) -> Option<Word>>(
        &self,
        loc: LocationCounter,
        get_symbol: F,
    ) -> Result<Word, EvalError>;
}

impl Eval for AtomicExpr {
    fn eval<F: FnMut(Symbol) -> Option<Word>>(
        &self,
        loc: LocationCounter,
        mut get_symbol: F,
    ) -> Result<Word, EvalError> {
        match &self.kind {
            AtomicExprKind::Location => Ok(Word::from(loc)),
            &AtomicExprKind::Symbol(symbol) => {
                get_symbol(symbol).ok_or_else(|| EvalError {
                    span: self.span,
                    kind: EvalErrorKind::UndefinedSymbol { symbol },
                })
            }
            &AtomicExprKind::Number(number) => {
                Word::try_from(number).map_err(|_| EvalError {
                    span: self.span,
                    kind: EvalErrorKind::NumberOutOfRange { number },
                })
            }
        }
    }
}

impl Eval for Expr {
    fn eval<F: FnMut(Symbol) -> Option<Word>>(
        &self,
        loc: LocationCounter,
        mut get_symbol: F,
    ) -> Result<Word, EvalError> {
        let mut value = self.head.eval(loc, &mut get_symbol)?;

        if self.sign == Some(Sign::Minus) {
            value = -value;
        }

        for (bin_op, atomic_expr) in &self.tail {
            let rhs = atomic_expr.eval(loc, &mut get_symbol)?;

            value = match bin_op {
                ExprBinOp::Add => Word::add(value, rhs).0,
                ExprBinOp::Sub => Word::sub(value, rhs).0,
                // Get the low word of mul.
                ExprBinOp::Mul => Word::mul(value, rhs).1,
                ExprBinOp::Div => {
                    Word::div(
                        // This ensures the numerator has `value`'s sign.
                        if value.sign() == Sign::Plus {
                            Word::POS_ZERO
                        } else {
                            Word::NEG_ZERO
                        },
                        value,
                        rhs,
                    )
                    .0
                }
                ExprBinOp::HighDiv => Word::div(value, Word::POS_ZERO, rhs).0,
                ExprBinOp::Colon => {
                    const WORD8: Word =
                        Word::from_sign_u32(Sign::Plus, 8).unwrap();

                    // value:rhs = 8 * value + rhs
                    Word::add(Word::mul(value, WORD8).1, rhs).0
                }
            }
        }

        Ok(value)
    }
}

impl Eval for WValue {
    fn eval<F: FnMut(Symbol) -> Option<Word>>(
        &self,
        loc: LocationCounter,
        mut get_symbol: F,
    ) -> Result<Word, EvalError> {
        let mut value = Word::POS_ZERO;

        for (expr, f_part) in &self.parts {
            let expr_value = expr.eval(loc, &mut get_symbol)?;

            value = match &f_part.kind {
                FPartKind::Empty => expr_value,
                FPartKind::Expr(f_part_expr) => {
                    let f_part_val = f_part_expr.eval(loc, &mut get_symbol)?;

                    Byte::try_from(f_part_val)
                        .ok()
                        .and_then(|field| expr_value.store(value, field))
                        .ok_or_else(|| EvalError {
                            span: f_part.span,
                            kind: EvalErrorKind::FieldOutOfRange {
                                value: f_part_val,
                            },
                        })?
                }
            }
        }

        Ok(value)
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use crate::symbol::SymbolName;

    use super::*;

    #[test]
    fn atomic_expr_eval_err_undefined_symbol() {
        let src = "SYM";
        let atomic_expr = AtomicExpr::from_str(src).unwrap();
        let loc = LocationCounter::try_from(100).unwrap();

        assert_eq!(
            atomic_expr.eval(loc, |_| None),
            Err(EvalError {
                span: atomic_expr.span,
                kind: EvalErrorKind::UndefinedSymbol {
                    symbol: atomic_expr.kind.as_symbol().unwrap().clone()
                }
            })
        );
    }

    #[test]
    fn atomic_expr_eval_err_number_out_of_range() {
        let src = "9999999999";
        let atomic_expr = AtomicExpr::from_str(src).unwrap();
        let loc = LocationCounter::try_from(100).unwrap();

        assert_eq!(
            atomic_expr.eval(loc, |_| None),
            Err(EvalError {
                span: atomic_expr.span,
                kind: EvalErrorKind::NumberOutOfRange {
                    number: *atomic_expr.kind.as_number().unwrap()
                }
            })
        );
    }

    #[test]
    fn atomic_expr_eval_ok_location() {
        let src = "*";
        let atomic_expr = AtomicExpr::from_str(src).unwrap();
        let loc = LocationCounter::try_from(100).unwrap();
        let value = Word::try_from(100).unwrap();

        assert_eq!(atomic_expr.eval(loc, |_| None), Ok(value));
    }

    #[test]
    fn atomic_expr_eval_ok_symbol() {
        let src = "SYM";
        let atomic_expr = AtomicExpr::from_str(src).unwrap();
        let loc = LocationCounter::try_from(100).unwrap();
        let symbol = Symbol::NonLocal(SymbolName::from_str("SYM").unwrap());
        let value = Word::try_from(500).unwrap();
        let get_symbol = |s| {
            assert_eq!(s, symbol);
            Some(value)
        };

        assert_eq!(atomic_expr.eval(loc, get_symbol), Ok(value));
    }

    #[test]
    fn atomic_expr_eval_ok_number() {
        let src = "123";
        let atomic_expr = AtomicExpr::from_str(src).unwrap();
        let loc = LocationCounter::try_from(100).unwrap();

        assert_eq!(
            atomic_expr.eval(loc, |_| None),
            Ok(Word::try_from(123).unwrap())
        );
    }

    #[test]
    fn expr_eval_fail_in_atomic_head() {
        let src = "SYM+0";
        let expr = Expr::from_str(src).unwrap();
        let loc = LocationCounter::try_from(100).unwrap();

        assert!(expr.eval(loc, |_| None).is_err());
    }

    #[test]
    fn expr_eval_fail_in_atomic_tail() {
        let src = "0+SYM";
        let expr = Expr::from_str(src).unwrap();
        let loc = LocationCounter::try_from(100).unwrap();

        assert!(expr.eval(loc, |_| None).is_err());
    }

    #[test]
    fn expr_eval_ok() {
        let loc = LocationCounter::try_from(100).unwrap();

        for (src, value) in [
            ("1+2", 3),
            ("1-2", -1),
            ("2*3", 6),
            ("100/6", 16),
            ("-100/6", -16),
            ("1//3", 357913941),
            ("1:3", 11),
            ("-1+5*20/6", 13),
        ] {
            let expr = Expr::from_str(src).unwrap();
            let word = Word::try_from(value).unwrap();

            assert_eq!(expr.eval(loc, |_| None), Ok(word));
        }
    }

    #[test]
    fn wvalue_eval_fail_in_expr() {
        let loc = LocationCounter::try_from(100).unwrap();

        for src in ["A", "0,A"] {
            let w_value = WValue::from_str(src).unwrap();

            assert!(w_value.eval(loc, |_| None).is_err());
        }
    }

    #[test]
    fn wvalue_eval_err_field_out_of_range() {
        let loc = LocationCounter::try_from(100).unwrap();

        for (src, value) in [("0(999999)", 999999), ("0(8)", 8)] {
            let w_value = WValue::from_str(src).unwrap();
            let f_part = &w_value.head().1;

            assert_eq!(
                w_value.eval(loc, |_| None),
                Err(EvalError {
                    span: f_part.span,
                    kind: EvalErrorKind::FieldOutOfRange {
                        value: Word::try_from(value).unwrap()
                    }
                })
            );
        }
    }

    #[test]
    fn wvalue_eval_ok() {
        let loc = LocationCounter::try_from(100).unwrap();

        for (src, value) in
            [("1", 1), ("0,1", 1), ("0,1(0:5)", 1), ("-1,0(1:3)", -1)]
        {
            let w_value = WValue::from_str(src).unwrap();
            let word = Word::try_from(value).unwrap();

            assert_eq!(w_value.eval(loc, |_| None), Ok(word));
        }
    }
}
