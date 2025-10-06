use std::sync::Arc;

use color_eyre::eyre::{ContextCompat, Result, bail};
use tracing::instrument;

use crate::{
    ast::{IdentRef, Type},
    codegen::{
        CodegenCtx, DefinitionIdent, TempoaryIdent,
        clac::{ClacProgram, ClacToken},
    },
};

pub trait TokenConsumer<'a> {
    fn consume(&mut self, token: ClacToken) -> Result<()>;
    fn ctx(&mut self) -> &mut CodegenCtx<'a>;

    fn consume_silent(&mut self, token: ClacToken) -> Result<()> {
        self.consume(ClacToken::Silent(Box::new(token)))
    }
}

impl<'a> TokenConsumer<'a> for &mut CodegenCtx<'a> {
    #[instrument]
    fn consume(&mut self, token: ClacToken) -> Result<()> {
        self.push_token(token)
    }

    fn ctx(&mut self) -> &mut CodegenCtx<'a> {
        self
    }
}

impl<'a> TokenConsumer<'a> for (&mut ClacProgram, &mut CodegenCtx<'a>) {
    #[instrument]
    fn consume(&mut self, token: ClacToken) -> Result<()> {
        self.0.0.push(token);

        Ok(())
    }

    fn ctx(&mut self) -> &mut CodegenCtx<'a> {
        self.1
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DataReference<'a> {
    Number(i32),
    Local(IdentRef<'a>),
    Const(IdentRef<'a>),
    Tempoary(TempoaryIdent),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FunctionSignature<'a> {
    pub arguements: Vec<(Type, IdentRef<'a>)>,
    pub return_type: Type,
}

impl FunctionSignature<'_> {
    pub fn paramater_width(&self) -> u32 {
        self.arguements
            .iter()
            .map(|(var_type, _)| var_type.width())
            .sum::<u32>()
    }

    pub fn return_width(&self) -> u32 {
        self.return_type.width()
    }

    pub fn stack_delta(&self) -> i32 {
        self.return_width() as i32 - self.paramater_width() as i32
    }
}

#[derive(Debug, Clone)]
pub enum ClacOp<'a> {
    Print {
        value: DataReference<'a>,
    },
    Quit,
    Add {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Sub {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Mul {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Div {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Mod {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Pow {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Lt {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Gt {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Le {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Ge {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Eq {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Ne {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    Neg {
        value: DataReference<'a>,
    },
    Not {
        value: DataReference<'a>,
    },
    LAnd {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    LOr {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    BShl {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    BShr {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    BAnd {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    If {
        condition: DataReference<'a>,
        on_true: DefinitionIdent<'a>,
        on_false: Option<DefinitionIdent<'a>>,
    },
    Call {
        name: DefinitionIdent<'a>,
        parameters: Vec<DataReference<'a>>,
    },
    Inline {
        parameters: Vec<DataReference<'a>>,
        signature: Arc<FunctionSignature<'a>>,
        tokens: Arc<Vec<ClacToken>>,
    },
}

impl<'a> ClacOp<'a> {
    #[instrument(skip(ctx))]
    pub fn load_inputs(&self, ctx: &mut CodegenCtx<'a>) -> Result<()> {
        match self {
            ClacOp::Print { value } => ctx.bring_up_references(&[*value], 1),
            ClacOp::Quit => Ok(()),
            ClacOp::Add { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::Sub { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::Mul { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::Div { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::Mod { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::Pow { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::Lt { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            // lhs and rhs reversed to save an instruction
            ClacOp::Gt { lhs, rhs } => ctx.bring_up_references(&[*rhs, *lhs], 2),
            // lhs and rhs reversed to save an instruction
            ClacOp::Le { lhs, rhs } => ctx.bring_up_references(&[*rhs, *lhs], 2),
            ClacOp::Ge { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::Eq { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::Ne { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::Neg { value } => ctx.bring_up_references(&[*value], 1),
            ClacOp::Not { value } => ctx.bring_up_references(&[*value], 1),
            ClacOp::LAnd { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::LOr { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::BShl { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::BShr { lhs, rhs } => ctx.bring_up_references(&[*lhs, *rhs], 2),
            ClacOp::BAnd { lhs, rhs: _rhs } => ctx.bring_up_references(&[*lhs], 1),
            ClacOp::If { condition, .. } => ctx.bring_up_references(&[*condition], 1),
            ClacOp::Call { name, parameters } => {
                let (_mangled, def) = ctx.lookup_definition(*name).expect("Call valid definition");
                ctx.bring_up_references(parameters, def.paramater_width())
            }
            ClacOp::Inline {
                parameters,
                signature,
                ..
            } => ctx.bring_up_references(parameters, signature.paramater_width()),
        }
    }

    #[instrument(skip(out))]
    pub fn execute<C: TokenConsumer<'a>>(&self, mut out: C) -> Result<Type> {
        let return_type = match self {
            ClacOp::Print { .. } => {
                out.consume(ClacToken::Print)?;
                Type::Void
            }
            ClacOp::Quit => {
                out.consume(ClacToken::Quit)?;
                Type::Void
            }
            ClacOp::Add { .. } => {
                out.consume(ClacToken::Add)?;
                Type::Int
            }
            ClacOp::Sub { .. } => {
                out.consume(ClacToken::Sub)?;
                Type::Int
            }
            ClacOp::Mul { .. } => {
                out.consume(ClacToken::Mul)?;
                Type::Int
            }
            ClacOp::Div { .. } => {
                out.consume(ClacToken::Div)?;
                Type::Int
            }
            ClacOp::Mod { .. } => {
                out.consume(ClacToken::Mod)?;
                Type::Int
            }
            ClacOp::Pow { .. } => {
                out.consume(ClacToken::Pow)?;
                Type::Int
            }
            ClacOp::Lt { .. } => {
                out.consume(ClacToken::Lt)?;
                Type::Bool
            }
            ClacOp::Gt { .. } => {
                // lhs and rhs reversed to save an instruction
                out.consume(ClacToken::Lt)?;
                Type::Bool
            }
            ClacOp::Le { .. } => {
                // lhs and rhs reversed to save an instruction
                out.consume(ClacToken::Lt)?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;
                Type::Bool
            }
            ClacOp::Ge { .. } => {
                out.consume(ClacToken::Lt)?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;
                Type::Bool
            }
            ClacOp::Eq { .. } => {
                out.consume(ClacToken::Sub)?;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(0))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume_silent(ClacToken::Number(1))?;

                Type::Bool
            }
            ClacOp::Ne { .. } => {
                out.consume(ClacToken::Sub)?;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume_silent(ClacToken::Number(0))?;

                Type::Bool
            }
            ClacOp::Neg { .. } => {
                out.consume(ClacToken::Number(0))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;
                Type::Int
            }
            ClacOp::Not { .. } => {
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;
                Type::Bool
            }
            ClacOp::LAnd { .. } => {
                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume_silent(ClacToken::Number(0))?;

                out.consume(ClacToken::Swap)?;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume_silent(ClacToken::Number(0))?;

                out.consume(ClacToken::Mul)?;

                Type::Bool
            }
            ClacOp::LOr { .. } => {
                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(0))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume_silent(ClacToken::Number(1))?;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(0))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume_silent(ClacToken::Number(1))?;

                out.consume(ClacToken::Mul)?;

                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;

                Type::Int
            }
            ClacOp::BShl { .. } => {
                out.consume(ClacToken::Number(2))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Pow)?;
                out.consume(ClacToken::Mul)?;
                Type::Int
            }
            ClacOp::BShr { .. } => {
                out.consume(ClacToken::Number(2))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Pow)?;
                out.consume(ClacToken::Div)?;
                Type::Int
            }
            ClacOp::BAnd { rhs, .. } => {
                let DataReference::Number(rhs) = *rhs else {
                    bail!(
                        "Bit wise and is only implemented for anding with a literal int, or an int that ends up getting inlined"
                    );
                };
                let mut rhs = rhs as u32;

                out.consume(ClacToken::Number(0))?;

                // This version doesnt work with negative inputs
                // // This is more complicated than I expected
                // let mut total_shift = 0;
                // while rhs.count_ones() > 0 {
                //     let trailing = rhs.trailing_ones();
                //
                //     out.consume(ClacToken::Number(2))?;
                //     out.consume(ClacToken::Pick)?;
                //     if total_shift > 0 {
                //         out.consume(ClacToken::Number(2i32.pow(total_shift)))?;
                //         out.consume(ClacToken::Div)?;
                //     }
                //     out.consume(ClacToken::Number(2i32.pow(trailing)))?;
                //     out.consume(ClacToken::Mod)?;
                //     if total_shift > 0 {
                //         out.consume(ClacToken::Number(2i32.pow(total_shift)))?;
                //         out.consume(ClacToken::Mul)?;
                //     }
                //     out.consume(ClacToken::Add)?;
                //
                //     total_shift += trailing;
                //     rhs >>= trailing;
                //     if rhs != 0 {
                //         total_shift += rhs.trailing_zeros();
                //         rhs >>= rhs.trailing_zeros();
                //     } else {
                //         break;
                //     }
                // }

                // This is more complicated than I expected
                let mut total_shift = 0;
                while rhs.count_ones() > 0 {
                    let trailing = rhs.trailing_ones();

                    for _ in 0..trailing {
                        out.consume(ClacToken::Number(2))?;
                        out.consume(ClacToken::Pick)?;
                        if total_shift > 0 {
                            out.consume(ClacToken::Number(2i32.pow(total_shift)))?;
                            out.consume(ClacToken::Div)?;
                        }
                        out.consume(ClacToken::Number(2))?;
                        out.consume(ClacToken::Mod)?;
                        out.consume(ClacToken::Number(1))?;
                        out.consume(ClacToken::Pick)?;
                        out.consume(ClacToken::Mul)?;

                        if total_shift > 0 {
                            out.consume(ClacToken::Number(2i32.pow(total_shift)))?;
                            out.consume(ClacToken::Mul)?;
                        }
                        out.consume(ClacToken::Add)?;
                        total_shift += 1;
                    }

                    rhs >>= trailing;
                    if rhs != 0 {
                        total_shift += rhs.trailing_zeros();
                        rhs >>= rhs.trailing_zeros();
                    } else {
                        break;
                    }
                }

                Type::Int
            }
            ClacOp::If {
                on_true, on_false, ..
            } => {
                let (on_true_impl, def_true) = out
                    .ctx()
                    .lookup_definition(*on_true)
                    .wrap_err_with(|| format!("Unknown if on_true definition, '{on_true:?}'"))?;

                if let Some(on_false) = on_false {
                    let (on_false_impl, def_false) =
                        out.ctx().lookup_definition(*on_false).wrap_err_with(|| {
                            format!("Unknown if false_true definition, '{on_true:?}'")
                        })?;

                    assert_eq!(def_true, def_false);

                    out.consume(ClacToken::If)?;
                    out.consume(on_true_impl)?;
                    out.consume(ClacToken::Number(1))?;
                    out.consume(ClacToken::Skip)?;
                    out.consume_silent(on_false_impl)?;

                    def_true.return_type
                } else {
                    assert!(def_true.stack_delta() <= 0);
                    assert!(def_true.return_width() == 0);

                    out.consume(ClacToken::If)?;
                    out.consume(on_true_impl)?;
                    out.consume(ClacToken::Number(-def_true.stack_delta()))?;
                    out.consume(ClacToken::Skip)?;

                    for _ in 0..-def_true.stack_delta() {
                        out.consume_silent(ClacToken::Drop)?;
                    }

                    Type::Void
                }
            }
            ClacOp::Call { name, .. } => {
                let (func_impl, def) = out
                    .ctx()
                    .lookup_definition(*name)
                    .expect("Call valid definition");
                let return_type = def.return_type;

                out.consume(func_impl)?;

                return_type
            }
            ClacOp::Inline {
                tokens, signature, ..
            } => {
                for token in tokens.iter() {
                    out.consume(token.clone())?;
                }

                signature.return_type
            }
        };

        Ok(return_type)
    }

    #[instrument(skip(ctx))]
    pub fn append_into(&self, ctx: &mut CodegenCtx<'a>) -> Result<TempoaryIdent> {
        self.load_inputs(ctx)?;
        let return_type = self.execute(&mut *ctx)?;

        Ok(ctx.allocate_tempoary(return_type))
    }
}
