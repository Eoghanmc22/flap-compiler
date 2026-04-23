use std::{backtrace::Backtrace, sync::Arc};

use crate::{
    ast::{FunctionSignature, IdentRef, Type, Value, VariableVersion},
    codegen::{
        CodegenCtx, DefinitionIdent, Offset, TempoaryIdent,
        clac::{ClacProgram, ClacToken, ClacValue, ClacValueUnsigned},
    },
    error::CodegenError,
};

type Result<'a, T, E = CodegenError<'a>> = std::result::Result<T, E>;

pub trait TokenConsumer<'a, 'b> {
    fn consume(&mut self, token: ClacToken) -> Result<'a, ()>;
    fn ctx(&mut self) -> &mut CodegenCtx<'a, 'b>;

    fn consume_silent(&mut self, token: ClacToken) -> Result<'a, ()> {
        self.consume(ClacToken::Silent(Box::new(token)))
    }
}

impl<'a, 'b> TokenConsumer<'a, 'b> for &mut CodegenCtx<'a, 'b> {
    fn consume(&mut self, token: ClacToken) -> Result<'a, ()> {
        self.push_token(token)
    }

    fn ctx(&mut self) -> &mut CodegenCtx<'a, 'b> {
        self
    }
}

impl<'a, 'b> TokenConsumer<'a, 'b> for (&mut ClacProgram, &mut CodegenCtx<'a, 'b>) {
    fn consume(&mut self, token: ClacToken) -> Result<'a, ()> {
        self.0.0.push(token);

        Ok(())
    }

    fn ctx(&mut self) -> &mut CodegenCtx<'a, 'b> {
        self.1
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DerivedFrom {
    pub version: VariableVersion,
    pub offset: Offset,
}

#[derive(Debug, Clone)]
pub enum DataReference<'a> {
    Value(Value<'a>, Option<DerivedFrom>),
    Local(VariableVersion, IdentRef<'a>),
    Const(VariableVersion, IdentRef<'a>),
    Tempoary(TempoaryIdent, Option<DerivedFrom>),
}

impl<'a> DataReference<'a> {
    pub fn as_clac_value(&self) -> Option<(ClacValue, Type<'a>)> {
        match self {
            DataReference::Value(value, _) => match value.as_repr()[..] {
                [int] => Some((int, value.compute_type())),
                _ => None,
            },
            _ => None,
        }
    }

    pub fn mark_originator(&self, version: VariableVersion, offset: Offset) -> Self {
        match self {
            DataReference::Tempoary(tempoary_ident, _derived_from_local) => {
                let new = DerivedFrom { version, offset };

                DataReference::Tempoary(*tempoary_ident, Some(new))
            }
            DataReference::Value(value, _derived_from_local) => {
                let new = DerivedFrom { version, offset };

                DataReference::Value(value.clone(), Some(new))
            }
            _ => self.clone(),
        }
    }

    pub fn originator(&self) -> Option<DerivedFrom> {
        match self {
            DataReference::Local(local, _) => Some(DerivedFrom {
                version: *local,
                offset: Offset(0),
            }),
            DataReference::Const(constant, _) => Some(DerivedFrom {
                version: *constant,
                offset: Offset(0),
            }),
            DataReference::Tempoary(_, derived_from_local) => derived_from_local.clone(),
            DataReference::Value(_, derived_from_local) => derived_from_local.clone(),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ClacOp<'a> {
    Print {
        value: DataReference<'a>,
    },
    Quit,
    IAdd {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    ISub {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    IMul {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    IDiv {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    FAdd {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    FSub {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    FMul {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    FDiv {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    IMod {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    IPow {
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
    Inv {
        value: DataReference<'a>,
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
    BOr {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    BXor {
        lhs: DataReference<'a>,
        rhs: DataReference<'a>,
    },
    If {
        condition: DataReference<'a>,
        on_true: DefinitionIdent<'a>,
        on_false: DefinitionIdent<'a>,
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
    pub fn load_inputs(&self, ctx: &mut CodegenCtx<'a, '_>) -> Result<'a, ()> {
        match self {
            ClacOp::Print { value } => ctx.bring_up_references([value], 1),
            ClacOp::Quit => Ok(()),
            ClacOp::IAdd { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::ISub { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::IMul { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::IDiv { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::IMod { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::IPow { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::FAdd { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::FSub { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::FMul { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::FDiv { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::Lt { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            // lhs and rhs reversed to save an instruction
            ClacOp::Gt { lhs, rhs } => ctx.bring_up_references([rhs, lhs], 2),
            // lhs and rhs reversed to save an instruction
            ClacOp::Le { lhs, rhs } => ctx.bring_up_references([rhs, lhs], 2),
            ClacOp::Ge { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::Eq { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::Ne { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::Inv { value } => ctx.bring_up_references([value], 1),
            ClacOp::Neg { value } => ctx.bring_up_references([value], 1),
            ClacOp::Not { value } => ctx.bring_up_references([value], 1),
            ClacOp::LAnd { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::LOr { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::BShl { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::BShr { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::BAnd { lhs, rhs } => {
                if rhs.as_clac_value().is_some() {
                    ctx.bring_up_references([lhs], 1)
                } else if lhs.as_clac_value().is_some() {
                    ctx.bring_up_references([rhs], 1)
                } else {
                    ctx.bring_up_references([lhs, rhs], 2)
                }
            }
            ClacOp::BOr { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::BXor { lhs, rhs } => ctx.bring_up_references([lhs, rhs], 2),
            ClacOp::If { condition, .. } => ctx.bring_up_references([condition], 1),
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

    pub fn execute<C: TokenConsumer<'a, 'b>>(&self, mut out: C) -> Result<'a, Type<'a>> {
        let mut call_lang_item = |name: &str| -> Result<'a, Type<'a>> {
            // TODO: improve
            let (func_impl, def) = out
                .ctx()
                .lookup_function_like_signature("bwor")
                .expect("Call valid definition");
            let func_impl = func_impl.to_vec();
            let ret = def.return_type.clone();

            for token in func_impl {
                out.consume(token)?;
            }

            Ok(ret)
        };

        let return_type = match self {
            ClacOp::Print { .. } => {
                out.consume(ClacToken::Print)?;
                Type::Void
            }
            ClacOp::Quit => {
                out.consume(ClacToken::Quit)?;
                Type::Void
            }
            ClacOp::IAdd { .. } => {
                out.consume(ClacToken::Add)?;
                Type::Int
            }
            ClacOp::ISub { .. } => {
                out.consume(ClacToken::Sub)?;
                Type::Int
            }
            ClacOp::IMul { .. } => {
                out.consume(ClacToken::Mul)?;
                Type::Int
            }
            ClacOp::IDiv { .. } => {
                out.consume(ClacToken::Div)?;
                Type::Int
            }
            ClacOp::IMod { .. } => {
                out.consume(ClacToken::Mod)?;
                Type::Int
            }
            ClacOp::IPow { .. } => {
                out.consume(ClacToken::Pow)?;
                Type::Int
            }
            ClacOp::FAdd { .. } => call_lang_item("__addsf3")?,
            ClacOp::FSub { .. } => call_lang_item("__subsf3")?,
            ClacOp::FMul { .. } => call_lang_item("__mulsf3")?,
            ClacOp::FDiv { .. } => call_lang_item("__divsf3")?,
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
            ClacOp::Inv { .. } => {
                out.consume(ClacToken::Number(-1))?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;
                Type::Int
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

                out.consume(ClacToken::Number(2))?;
                out.consume(ClacToken::Pick)?;
                out.consume(ClacToken::Number(2))?;
                out.consume(ClacToken::Pick)?;
                out.consume(ClacToken::Mod)?;

                out.consume(ClacToken::Number(2))?;
                out.consume(ClacToken::Pick)?;
                out.consume(ClacToken::Add)?;

                out.consume(ClacToken::Number(2))?;
                out.consume(ClacToken::Pick)?;
                out.consume(ClacToken::Mod)?;

                // a 2^b (a mod 2^b)

                out.consume(ClacToken::Rot)?;
                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Sub)?;

                // 2^b (a - a mod 2^b)

                out.consume(ClacToken::Swap)?;
                out.consume(ClacToken::Div)?;

                Type::Int
            }
            ClacOp::BAnd { lhs, rhs } => {
                match (lhs.as_clac_value(), rhs.as_clac_value()) {
                    (Some((literal, _)), _) | (_, Some((literal, _))) => {
                        if literal == -1 {
                            return Ok(Type::Int);
                        }

                        let mut literal = literal as ClacValueUnsigned;

                        out.consume(ClacToken::Number(0))?;

                        let mut total_shift = 0;
                        while literal.count_ones() > 0 {
                            let trailing = literal.trailing_ones();
                            let mod_factor = (2 as ClacValue).pow(trailing);
                            let shift_factor = (2 as ClacValue).pow(total_shift);

                            out.consume(ClacToken::Number(2))?;
                            out.consume(ClacToken::Pick)?;
                            if total_shift > 0 {
                                // floor div correction
                                out.consume(ClacToken::Number(1))?;
                                out.consume(ClacToken::Pick)?;
                                out.consume(ClacToken::Number(shift_factor))?;
                                out.consume(ClacToken::Mod)?;
                                out.consume(ClacToken::Number(shift_factor))?;
                                out.consume(ClacToken::Add)?;
                                out.consume(ClacToken::Number(shift_factor))?;
                                out.consume(ClacToken::Mod)?;
                                out.consume(ClacToken::Sub)?;

                                out.consume(ClacToken::Number(shift_factor))?;
                                out.consume(ClacToken::Div)?;
                            }

                            out.consume(ClacToken::Number(mod_factor))?;
                            out.consume(ClacToken::Mod)?;
                            out.consume(ClacToken::Number(mod_factor))?;
                            out.consume(ClacToken::Add)?;
                            out.consume(ClacToken::Number(mod_factor))?;
                            out.consume(ClacToken::Mod)?;

                            if total_shift > 0 {
                                out.consume(ClacToken::Number(shift_factor))?;
                                out.consume(ClacToken::Mul)?;
                            }
                            out.consume(ClacToken::Add)?;

                            total_shift += trailing;
                            literal >>= trailing;
                            if literal != 0 {
                                total_shift += literal.trailing_zeros();
                                literal >>= literal.trailing_zeros();
                            } else {
                                break;
                            }
                        }

                        Type::Int
                    }
                    (None, None) => call_lang_item("bwand")?,
                }
            }
            ClacOp::BOr { .. } => call_lang_item("bwor")?,
            ClacOp::BXor { .. } => call_lang_item("bwxor")?,
            ClacOp::If {
                on_true, on_false, ..
            } => {
                let (on_true_impl, def_true) = out.ctx().lookup_definition(*on_true)?;
                let on_true_impl = on_true_impl.to_vec();
                let def_true = def_true.clone();

                let (on_false_impl, def_false) = out.ctx().lookup_definition(*on_false)?;
                let on_false_impl = on_false_impl.to_vec();
                let def_false = def_false.clone();

                assert_eq!(
                    def_true.stack_delta(out.ctx().type_checker)?,
                    def_false.stack_delta(out.ctx().type_checker)?
                );

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
            }
            ClacOp::Call { name, .. } => {
                let (func_impl, def) = out
                    .ctx()
                    .lookup_definition(*name)
                    .expect("Call valid definition");
                let func_impl = func_impl.to_vec();
                let ret = def.return_type.clone();

                for token in func_impl {
                    out.consume(token)?;
                }

                ret
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

    pub fn try_execute_const(&self, _ctx: &mut CodegenCtx<'a, 'b>) -> Option<DataReference<'a>> {
        let ret = match self {
            ClacOp::IAdd { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(
                    Value::Cast(lhs_type.into(), Value::Int(lhs.wrapping_add(rhs)).into()),
                    None,
                )
            }
            ClacOp::ISub { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(
                    Value::Cast(lhs_type, Value::Int(lhs.wrapping_sub(rhs)).into()),
                    None,
                )
            }
            ClacOp::IMul { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(
                    Value::Cast(lhs_type, Value::Int(lhs.wrapping_mul(rhs)).into()),
                    None,
                )
            }
            ClacOp::IDiv { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(
                    Value::Cast(lhs_type, Value::Int(lhs.wrapping_div(rhs)).into()),
                    None,
                )
            }
            ClacOp::FAdd { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                let lhs = f32::from_bits(lhs as _);
                let rhs = f32::from_bits(rhs as _);

                DataReference::Value(
                    Value::Cast(
                        lhs_type.into(),
                        Value::Int((lhs + rhs).to_bits() as _).into(),
                    ),
                    None,
                )
            }
            ClacOp::FSub { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                let lhs = f32::from_bits(lhs as _);
                let rhs = f32::from_bits(rhs as _);

                DataReference::Value(
                    Value::Cast(
                        lhs_type.into(),
                        Value::Int((lhs - rhs).to_bits() as _).into(),
                    ),
                    None,
                )
            }
            ClacOp::FMul { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                let lhs = f32::from_bits(lhs as _);
                let rhs = f32::from_bits(rhs as _);

                DataReference::Value(
                    Value::Cast(
                        lhs_type.into(),
                        Value::Int((lhs * rhs).to_bits() as _).into(),
                    ),
                    None,
                )
            }
            ClacOp::FDiv { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                let lhs = f32::from_bits(lhs as _);
                let rhs = f32::from_bits(rhs as _);

                DataReference::Value(
                    Value::Cast(
                        lhs_type.into(),
                        Value::Int((lhs / rhs).to_bits() as _).into(),
                    ),
                    None,
                )
            }
            ClacOp::IMod { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(
                    Value::Cast(lhs_type, Value::Int(lhs.wrapping_rem(rhs)).into()),
                    None,
                )
            }
            ClacOp::IPow { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(
                    Value::Cast(lhs_type, Value::Int(lhs.wrapping_pow(rhs as u32)).into()),
                    None,
                )
            }
            ClacOp::Lt { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs < rhs), None)
            }
            ClacOp::Gt { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs > rhs), None)
            }
            ClacOp::Le { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs <= rhs), None)
            }
            ClacOp::Ge { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs >= rhs), None)
            }
            ClacOp::Eq { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs == rhs), None)
            }
            ClacOp::Ne { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs != rhs), None)
            }
            ClacOp::Inv { value } => {
                let (value, value_type) = value.as_clac_value()?;

                DataReference::Value(Value::Cast(value_type, Value::Int(!value).into()), None)
            }
            ClacOp::Neg { value } => {
                let (value, value_type) = value.as_clac_value()?;

                DataReference::Value(Value::Cast(value_type, Value::Int(-value).into()), None)
            }
            ClacOp::Not { value } => {
                let (value, _value_type) = value.as_clac_value()?;

                DataReference::Value(Value::Bool(value == 0), None)
            }
            ClacOp::LAnd { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs != 0 && rhs != 0), None)
            }
            ClacOp::LOr { lhs, rhs } => {
                let (lhs, _lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Bool(lhs != 0 || rhs != 0), None)
            }
            ClacOp::BShl { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(
                    Value::Cast(lhs_type, Value::Int(lhs.unbounded_shl(rhs as u32)).into()),
                    None,
                )
            }
            ClacOp::BShr { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(
                    Value::Cast(lhs_type, Value::Int(lhs.unbounded_shr(rhs as u32)).into()),
                    None,
                )
            }
            ClacOp::BAnd { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(lhs_type, Value::Int(lhs & rhs).into()), None)
            }
            ClacOp::BOr { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(lhs_type, Value::Int(lhs | rhs).into()), None)
            }
            ClacOp::BXor { lhs, rhs } => {
                let (lhs, lhs_type) = lhs.as_clac_value()?;
                let (rhs, _rhs_type) = rhs.as_clac_value()?;

                DataReference::Value(Value::Cast(lhs_type, Value::Int(lhs ^ rhs).into()), None)
            }
            ClacOp::Print { .. }
            | ClacOp::Quit
            | ClacOp::If { .. }
            | ClacOp::Call { .. }
            | ClacOp::Inline { .. } => return None,
        };

        Some(ret)
    }

    pub fn append_into(&self, ctx: &mut CodegenCtx<'a, 'b>) -> Result<'a, DataReference<'a>> {
        if let Some(res) = self.try_execute_const(ctx) {
            return Ok(res);
        }

        self.load_inputs(ctx)?;
        let return_type = self.execute(&mut *ctx)?;

        Ok(DataReference::Tempoary(
            ctx.allocate_tempoary(return_type)?,
            None,
        ))
    }
}
