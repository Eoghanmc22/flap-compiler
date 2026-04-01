use std::sync::Arc;

use color_eyre::eyre::{ContextCompat, Result, bail};

use crate::{
    ast::{FunctionSignature, IdentRef, Type, Value},
    codegen::{
        CodegenCtx, DefinitionIdent, TempoaryIdent,
        clac::{ClacProgram, ClacToken, ClacValue, ClacValueUnsigned},
    },
};

pub trait TokenConsumer<'a, 'b> {
    fn consume(&mut self, token: ClacToken) -> Result<()>;
    fn ctx(&mut self) -> &mut CodegenCtx<'a, 'b>;

    fn consume_silent(&mut self, token: ClacToken) -> Result<()> {
        self.consume(ClacToken::Silent(Box::new(token)))
    }
}

impl<'a, 'b> TokenConsumer<'a, 'b> for &mut CodegenCtx<'a, 'b> {
    fn consume(&mut self, token: ClacToken) -> Result<()> {
        self.push_token(token)
    }

    fn ctx(&mut self) -> &mut CodegenCtx<'a, 'b> {
        self
    }
}

impl<'a, 'b> TokenConsumer<'a, 'b> for (&mut ClacProgram, &mut CodegenCtx<'a, 'b>) {
    fn consume(&mut self, token: ClacToken) -> Result<()> {
        self.0.0.push(token);

        Ok(())
    }

    fn ctx(&mut self) -> &mut CodegenCtx<'a, 'b> {
        self.1
    }
}

#[derive(Debug, Clone)]
pub enum DataReference<'a> {
    Value(Value<'a>),
    Local(IdentRef<'a>),
    Const(IdentRef<'a>),
    Tempoary(TempoaryIdent),
}

impl<'a> DataReference<'a> {
    pub fn as_clac_value(&self) -> Option<(ClacValue, Type<'a>)> {
        match self {
            DataReference::Value(value) => match value.as_repr()[..] {
                [int] => Some((int, value.compute_type())),
                _ => None,
            },
            _ => None,
        }
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

impl<'b, 'a: 'b> ClacOp<'a> {
    pub fn load_inputs(&self, ctx: &mut CodegenCtx<'a, '_>) -> Result<()> {
        match self {
            ClacOp::Print { value } => ctx.bring_up_references(&[value], 1),
            ClacOp::Quit => Ok(()),
            ClacOp::Add { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::Sub { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::Mul { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::Div { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::Mod { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::Pow { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::Lt { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            // lhs and rhs reversed to save an instruction
            ClacOp::Gt { lhs, rhs } => ctx.bring_up_references(&[rhs, lhs], 2),
            // lhs and rhs reversed to save an instruction
            ClacOp::Le { lhs, rhs } => ctx.bring_up_references(&[rhs, lhs], 2),
            ClacOp::Ge { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::Eq { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::Ne { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::Neg { value } => ctx.bring_up_references(&[value], 1),
            ClacOp::Not { value } => ctx.bring_up_references(&[value], 1),
            ClacOp::LAnd { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::LOr { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::BShl { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::BShr { lhs, rhs } => ctx.bring_up_references(&[lhs, rhs], 2),
            ClacOp::BAnd { lhs, rhs: _rhs } => ctx.bring_up_references(&[lhs], 1),
            ClacOp::If { condition, .. } => ctx.bring_up_references(&[condition], 1),
            ClacOp::Call { name, parameters } => {
                let (_mangled, def) = ctx.lookup_definition(*name).expect("Call valid definition");
                ctx.bring_up_references(parameters, def.paramater_width(ctx.type_checker)?)
            }
            ClacOp::Inline {
                parameters,
                signature,
                ..
            } => ctx.bring_up_references(parameters, signature.paramater_width(ctx.type_checker)?),
        }
    }

    pub fn execute<C: TokenConsumer<'a, 'b>>(&self, mut out: C) -> Result<Type<'a>> {
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
            // TODO: we can optimize this since the type checker makes sure
            // the inputs will be 1 or 0
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
            // TODO: we can optimize this since the type checker makes sure
            // the inputs will be 1 or 0
            ClacOp::LOr { .. } => {
                out.consume(ClacToken::If)?;
                out.consume(ClacToken::Number(0))?;
                out.consume(ClacToken::Number(1))?;
                out.consume(ClacToken::Skip)?;
                out.consume_silent(ClacToken::Number(1))?;

                out.consume(ClacToken::Swap)?;

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
                let DataReference::Value(Value::Int(rhs) | Value::Char(rhs)) = *rhs else {
                    bail!(
                        "Bit wise AND is only implemented for anding with a literal int, or an int that ends up getting inlined"
                    );
                };
                let mut rhs = rhs as ClacValueUnsigned;

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
                            out.consume(ClacToken::Number((2 as ClacValue).pow(total_shift)))?;
                            out.consume(ClacToken::Div)?;
                        }
                        out.consume(ClacToken::Number(2))?;
                        out.consume(ClacToken::Mod)?;
                        out.consume(ClacToken::Number(1))?;
                        out.consume(ClacToken::Pick)?;
                        out.consume(ClacToken::Mul)?;

                        if total_shift > 0 {
                            out.consume(ClacToken::Number((2 as ClacValue).pow(total_shift)))?;
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

                    match &on_true_impl[..] {
                        [] => out.consume(ClacToken::Drop)?,
                        [true_token] => {
                            out.consume(ClacToken::If)?;
                            out.consume(true_token.clone())?;
                            out.consume(ClacToken::Number(on_false_impl.len() as _))?;
                            out.consume(ClacToken::Skip)?;

                            for token in on_false_impl {
                                out.consume_silent(token)?;
                            }
                        }
                        [..] => {
                            out.consume(ClacToken::Number(on_false_impl.len() as ClacValue + 2))?;
                            out.consume(ClacToken::Mul)?;
                            out.consume(ClacToken::Skip)?;

                            for token in on_false_impl {
                                out.consume(token)?;
                            }

                            out.consume(ClacToken::Number(on_true_impl.len() as _))?;
                            out.consume(ClacToken::Skip)?;

                            for token in on_true_impl {
                                out.consume_silent(token)?;
                            }
                        }
                    }

                    def_true.return_type.clone()
                } else {
                    assert!(def_true.stack_delta(out.ctx().type_checker)? <= 0);
                    assert!(def_true.return_width(out.ctx().type_checker)? == 0);

                    let true_delta = def_true.stack_delta(out.ctx().type_checker)?;

                    match &on_true_impl[..] {
                        [] => out.consume(ClacToken::Drop)?,
                        [true_token] => {
                            out.consume(ClacToken::If)?;
                            out.consume(true_token.clone())?;
                            out.consume(ClacToken::Number(-true_delta))?;
                            out.consume(ClacToken::Skip)?;
                        }
                        [..] => {
                            out.consume(ClacToken::Number(1))?;
                            out.consume(ClacToken::Swap)?;
                            out.consume(ClacToken::Sub)?;

                            out.consume(ClacToken::Number(on_true_impl.len() as ClacValue + 2))?;
                            out.consume(ClacToken::Mul)?;
                            out.consume(ClacToken::Skip)?;

                            for token in on_true_impl {
                                out.consume(token)?;
                            }
                            out.consume(ClacToken::Number(-true_delta))?;
                            out.consume(ClacToken::Skip)?;
                        }
                    }

                    for _ in 0..-def_true.stack_delta(out.ctx().type_checker)? {
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

                for token in func_impl {
                    out.consume(token)?;
                }

                def.return_type.clone()
            }
            ClacOp::Inline {
                tokens, signature, ..
            } => {
                for token in tokens.iter() {
                    out.consume(token.clone())?;
                }

                signature.return_type.clone()
            }
        };

        Ok(return_type)
    }

    pub fn try_execute_const(&self, ctx: &mut CodegenCtx<'a, 'b>) -> Option<DataReference<'a>> {
        let ret = match self {
            ClacOp::Add { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(
                    lhs_type.into(),
                    Value::Int(lhs.wrapping_add(rhs)).into(),
                ))
            }
            ClacOp::Sub { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(
                    lhs_type,
                    Value::Int(lhs.wrapping_sub(rhs)).into(),
                ))
            }
            ClacOp::Mul { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(
                    lhs_type,
                    Value::Int(lhs.wrapping_mul(rhs)).into(),
                ))
            }
            ClacOp::Div { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(
                    lhs_type,
                    Value::Int(lhs.wrapping_div(rhs)).into(),
                ))
            }
            ClacOp::Mod { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(
                    lhs_type,
                    Value::Int(lhs.wrapping_rem(rhs)).into(),
                ))
            }
            ClacOp::Pow { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(
                    lhs_type,
                    Value::Int(lhs.wrapping_pow(rhs as u32)).into(),
                ))
            }
            ClacOp::Lt { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs < rhs))
            }
            ClacOp::Gt { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs > rhs))
            }
            ClacOp::Le { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs <= rhs))
            }
            ClacOp::Ge { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs >= rhs))
            }
            ClacOp::Eq { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs == rhs))
            }
            ClacOp::Ne { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs != rhs))
            }
            ClacOp::Neg { value } => {
                let (value, value_type) = value.as_clac_value()?;

                DataReference::Value(Value::Cast(value_type, Value::Int(-value).into()))
            }
            ClacOp::Not { value } => {
                let (value, _value_type) = value.as_clac_value()?;

                DataReference::Value(Value::Bool(value == 0))
            }
            ClacOp::LAnd { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs != 0 && rhs != 0))
            }
            ClacOp::LOr { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs != 0 || rhs != 0))
            }
            ClacOp::BShl { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(
                    lhs_type,
                    Value::Int(lhs.unbounded_shl(rhs as u32)).into(),
                ))
            }
            ClacOp::BShr { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(
                    lhs_type,
                    Value::Int(lhs.unbounded_shr(rhs as u32)).into(),
                ))
            }
            ClacOp::BAnd { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(lhs_type, Value::Int(lhs & rhs).into()))
            }
            _ => return None,
        };

        Some(ret)
    }

    pub fn append_into(&self, ctx: &mut CodegenCtx<'a, 'b>) -> Result<DataReference<'a>> {
        if let Some(res) = self.try_execute_const(ctx) {
            return Ok(res);
        }

        self.load_inputs(ctx)?;
        let return_type = self.execute(&mut *ctx)?;

        Ok(DataReference::Tempoary(ctx.allocate_tempoary(return_type)?))
    }
}
