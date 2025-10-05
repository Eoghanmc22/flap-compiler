use std::sync::Arc;

use color_eyre::eyre::{ContextCompat, Result, bail};

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
}

impl<'a> TokenConsumer<'a> for &mut CodegenCtx<'a> {
    fn consume(&mut self, token: ClacToken) -> Result<()> {
        self.push_token(token)
    }

    fn ctx(&mut self) -> &mut CodegenCtx<'a> {
        self
    }
}

impl<'a> TokenConsumer<'a> for (&mut ClacProgram, &mut CodegenCtx<'a>) {
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

    pub fn execute<C: TokenConsumer<'a>>(&self, mut out: C) -> Result<Option<TempoaryIdent>> {
        let mut result = None;

        match self {
            ClacOp::Print { .. } => {
                out.consume(ClacToken::Print)?;
            }
            ClacOp::Quit => {
                out.consume(ClacToken::Quit)?;
            }
            ClacOp::Add { .. } => {
                out.consume(ClacToken::Add)?;
                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::Sub { .. } => {
                out.consume(ClacToken::Sub)?;
                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::Mul { .. } => {
                out.consume(ClacToken::Mul)?;
                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::Div { .. } => {
                out.consume(ClacToken::Div)?;
                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::Mod { .. } => {
                out.consume(ClacToken::Mod)?;
                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::Pow { .. } => {
                out.consume(ClacToken::Pow)?;
                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::Lt { .. } => {
                out.consume(ClacToken::Lt)?;
                result = Some(out.ctx().allocate_tempoary(Type::Bool));
            }
            ClacOp::Gt { .. } => {
                // lhs and rhs reversed to save an instruction
                out.consume(ClacToken::Lt)?;
                result = Some(out.ctx().allocate_tempoary(Type::Bool));
            }
            ClacOp::Le { .. } => {
                // lhs and rhs reversed to save an instruction
                out.consume(ClacToken::Lt)?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;
                result = Some(out.ctx().allocate_tempoary(Type::Bool));
            }
            ClacOp::Ge { .. } => {
                out.consume(ClacToken::Rot)?;
                out.consume(ClacToken::Rot)?;
                out.consume(ClacToken::Lt)?;
                out.consume(ClacToken::Sub)?;
                result = Some(out.ctx().allocate_tempoary(Type::Bool));
            }
            ClacOp::Eq { .. } => {
                out.consume(ClacToken::Sub)?;

                let cursor_pos = out.ctx().cursor;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(0))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume(ClacToken::Number(1))?;

                // This avoids double counting the stack delta,
                // -1 from `if`, +1 from value load
                out.ctx().cursor = cursor_pos;

                result = Some(out.ctx().allocate_tempoary(Type::Bool));
            }
            ClacOp::Ne { .. } => {
                out.consume(ClacToken::Sub)?;

                let cursor_pos = out.ctx().cursor;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume(ClacToken::Number(0))?;

                // This avoids double counting the stack delta,
                // -1 from `if`, +1 from value load
                out.ctx().cursor = cursor_pos;

                result = Some(out.ctx().allocate_tempoary(Type::Bool));
            }
            ClacOp::Neg { .. } => {
                out.consume(ClacToken::Number(0))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;
                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::Not { .. } => {
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;
                result = Some(out.ctx().allocate_tempoary(Type::Bool));
            }
            ClacOp::LAnd { .. } => {
                let cursor_pos = out.ctx().cursor;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume(ClacToken::Number(0))?;

                out.consume(ClacToken::Swap)?;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume(ClacToken::Number(0))?;

                out.consume(ClacToken::Mul)?;

                // TODO: check
                // Actual delta is 1-2, computed i -3-2
                out.ctx().cursor = cursor_pos - 1;

                result = Some(out.ctx().allocate_tempoary(Type::Bool));
            }
            ClacOp::LOr { .. } => {
                let cursor_pos = out.ctx().cursor;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(0))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume(ClacToken::Number(1))?;

                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(0))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume(ClacToken::Number(1))?;

                out.consume(ClacToken::Mul)?;

                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;

                // TODO: check
                // Actual delta is 1-2, computed i -3-2
                out.ctx().cursor = cursor_pos - 1;

                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::BShl { .. } => {
                out.consume(ClacToken::Number(2))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Pow)?;
                out.consume(ClacToken::Mul)?;
                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::BShr { .. } => {
                out.consume(ClacToken::Number(2))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Pow)?;
                out.consume(ClacToken::Div)?;
                result = Some(out.ctx().allocate_tempoary(Type::Int));
            }
            ClacOp::BAnd { rhs, .. } => {
                let DataReference::Number(rhs) = *rhs else {
                    bail!(
                        "Bit wise and is only implemented for anding with a literal int, or an int that ends up getting inlined"
                    );
                };
                let mut rhs = rhs as u32;

                out.consume(ClacToken::Number(0))?;

                // This is more complicated than I expected
                let mut total_shift = 0;
                while rhs.count_ones() > 0 {
                    let trailing = rhs.trailing_ones();

                    out.consume(ClacToken::Number(2))?;
                    out.consume(ClacToken::Pick)?;
                    if total_shift > 0 {
                        out.consume(ClacToken::Number(2i32.pow(total_shift)))?;
                        out.consume(ClacToken::Div)?;
                    }
                    out.consume(ClacToken::Number(2i32.pow(trailing)))?;
                    out.consume(ClacToken::Mod)?;
                    if total_shift > 0 {
                        out.consume(ClacToken::Number(2i32.pow(total_shift)))?;
                        out.consume(ClacToken::Mul)?;
                    }
                    out.consume(ClacToken::Add)?;

                    total_shift += trailing;
                    rhs >>= trailing;
                    if rhs != 0 {
                        total_shift += rhs.trailing_zeros();
                        rhs >>= rhs.trailing_zeros();
                    } else {
                        break;
                    }
                }

                result = Some(out.ctx().allocate_tempoary(Type::Int));
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

                    let cursor_pos = out.ctx().cursor;

                    out.consume(ClacToken::Number(1))?;
                    out.consume(ClacToken::Skip)?;
                    out.consume(on_false_impl)?;

                    // This avoids double counting the stack delta,
                    // We will either hit on true or on false, never both
                    // This sets the counter back to the its value after the first call
                    out.ctx().cursor = cursor_pos;
                } else {
                    assert_eq!(def_true.stack_delta(), 0);

                    out.consume(ClacToken::If)?;
                    out.consume(on_true_impl)?;
                    out.consume(ClacToken::Number(0))?;
                    out.consume(ClacToken::Skip)?;
                }
            }
            ClacOp::Call { name, .. } => {
                let (func_impl, def) = out
                    .ctx()
                    .lookup_definition(*name)
                    .expect("Call valid definition");
                let return_type = def.return_type;

                out.consume(func_impl)?;

                result = Some(out.ctx().allocate_tempoary(return_type));
            }
            ClacOp::Inline {
                tokens, signature, ..
            } => {
                for token in tokens.iter() {
                    out.consume(token.clone())?;
                }

                result = Some(out.ctx().allocate_tempoary(signature.return_type));
            }
        }

        Ok(result)
    }

    pub fn append_into(&self, ctx: &mut CodegenCtx<'a>) -> Result<Option<TempoaryIdent>> {
        println!("Generating code for {self:?}");

        self.load_inputs(ctx)?;
        self.execute(ctx)
    }
}
