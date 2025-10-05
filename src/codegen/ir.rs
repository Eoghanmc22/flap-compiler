use color_eyre::eyre::{ContextCompat, Result, bail};

use crate::{
    ast::{IdentRef, Type},
    codegen::{CodegenCtx, DefinitionIdent, TempoaryIdent, clac::ClacToken},
};

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
}

impl<'a> ClacOp<'a> {
    pub fn append_into(&self, ctx: &mut CodegenCtx<'a>) -> Result<Option<TempoaryIdent>> {
        let mut result = None;

        println!("Generating code for {self:?}");

        match self {
            ClacOp::Print { value } => {
                ctx.bring_up_references(&[*value], 1)?;
                ctx.push_token(ClacToken::Print)?;
            }
            ClacOp::Quit => {
                ctx.push_token(ClacToken::Quit)?;
            }
            ClacOp::Add { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Add)?;
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Sub { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Sub)?;
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Mul { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Mul)?;
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Div { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Div)?;
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Mod { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Mod)?;
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Pow { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Pow)?;
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Lt { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Lt)?;
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Gt { lhs, rhs } => {
                // lhs and rhs reversed to save an instruction
                ctx.bring_up_references(&[*rhs, *lhs], 2)?;
                // ctx.push_token(ClacToken::Swap)?;
                ctx.push_token(ClacToken::Lt)?;
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Le { lhs, rhs } => {
                ctx.push_token(ClacToken::Number(1))?;
                // lhs and rhs reversed to save an instruction
                ctx.bring_up_references(&[*rhs, *lhs], 2)?;
                // ctx.push_token(ClacToken::Swap)?;
                ctx.push_token(ClacToken::Lt)?;
                ctx.push_token(ClacToken::Sub)?;
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Ge { lhs, rhs } => {
                ctx.push_token(ClacToken::Number(1))?;
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Lt)?;
                ctx.push_token(ClacToken::Sub)?;
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Eq { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Sub)?;

                let cursor_pos = ctx.cursor;

                ctx.push_token(ClacToken::If)?;
                ctx.push_token(ClacToken::Number(0))?;
                ctx.push_token(ClacToken::Number(1))?;
                ctx.push_token(ClacToken::Skip)?;
                ctx.push_token(ClacToken::Number(1))?;

                // This avoids double counting the stack delta,
                // -1 from `if`, +1 from value load
                ctx.cursor = cursor_pos;

                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Ne { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Sub)?;

                let cursor_pos = ctx.cursor;

                ctx.push_token(ClacToken::If)?;
                ctx.push_token(ClacToken::Number(1))?;
                ctx.push_token(ClacToken::Number(1))?;
                ctx.push_token(ClacToken::Skip)?;
                ctx.push_token(ClacToken::Number(0))?;

                // This avoids double counting the stack delta,
                // -1 from `if`, +1 from value load
                ctx.cursor = cursor_pos;

                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Neg { value } => {
                ctx.push_token(ClacToken::Number(0))?;
                ctx.bring_up_references(&[*value], 1)?;
                ctx.push_token(ClacToken::Sub)?;
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Not { value } => {
                ctx.push_token(ClacToken::Number(1))?;
                ctx.bring_up_references(&[*value], 1)?;
                ctx.push_token(ClacToken::Sub)?;
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::LAnd { lhs, rhs } => {
                let cursor_pos = ctx.cursor;

                ctx.bring_up_references(&[*lhs], 1)?;
                ctx.push_token(ClacToken::If)?;
                ctx.push_token(ClacToken::Number(1))?;
                ctx.push_token(ClacToken::Number(1))?;
                ctx.push_token(ClacToken::Skip)?;
                ctx.push_token(ClacToken::Number(0))?;

                ctx.bring_up_references(&[*rhs], 1)?;
                ctx.push_token(ClacToken::If)?;
                ctx.push_token(ClacToken::Number(1))?;
                ctx.push_token(ClacToken::Number(1))?;
                ctx.push_token(ClacToken::Skip)?;
                ctx.push_token(ClacToken::Number(0))?;

                ctx.push_token(ClacToken::Mul)?;

                // This avoids double counting the stack delta,
                // +1 from first `if`, +1 from second if, -1 from `mul`
                ctx.cursor = cursor_pos + 1;

                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::LOr { lhs, rhs } => {
                ctx.push_token(ClacToken::Number(1))?;

                let cursor_pos = ctx.cursor;

                ctx.bring_up_references(&[*lhs], 1)?;
                ctx.push_token(ClacToken::If)?;
                ctx.push_token(ClacToken::Number(0))?;
                ctx.push_token(ClacToken::Number(1))?;
                ctx.push_token(ClacToken::Skip)?;
                ctx.push_token(ClacToken::Number(1))?;

                ctx.bring_up_references(&[*rhs], 1)?;
                ctx.push_token(ClacToken::If)?;
                ctx.push_token(ClacToken::Number(0))?;
                ctx.push_token(ClacToken::Number(1))?;
                ctx.push_token(ClacToken::Skip)?;
                ctx.push_token(ClacToken::Number(1))?;

                ctx.push_token(ClacToken::Mul)?;
                ctx.push_token(ClacToken::Sub)?;

                // This avoids double counting the stack delta,
                // +1 from first `if`, +1 from second if, -1 from `mul`, -1 from `sub`
                ctx.cursor = cursor_pos;

                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::BShl { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Number(2))?;
                ctx.push_token(ClacToken::Swap)?;
                ctx.push_token(ClacToken::Pow)?;
                ctx.push_token(ClacToken::Mul)?;
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::BShr { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2)?;
                ctx.push_token(ClacToken::Number(2))?;
                ctx.push_token(ClacToken::Swap)?;
                ctx.push_token(ClacToken::Pow)?;
                ctx.push_token(ClacToken::Div)?;
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::BAnd { lhs, rhs } => {
                let DataReference::Number(rhs) = *rhs else {
                    bail!(
                        "Bit wise and is only implemented for anding with a literal int, or an int that ends up getting inlined"
                    );
                };
                let mut rhs = rhs as u32;

                ctx.bring_up_references(&[*lhs], 1)?;
                ctx.push_token(ClacToken::Number(0))?;

                // This is more complicated than I expected
                let mut total_shift = 0;
                while rhs.count_ones() > 0 {
                    let trailing = rhs.trailing_ones();

                    ctx.push_token(ClacToken::Number(2))?;
                    ctx.push_token(ClacToken::Pick)?;
                    if total_shift > 0 {
                        ctx.push_token(ClacToken::Number(2i32.pow(total_shift)))?;
                        ctx.push_token(ClacToken::Div)?;
                    }
                    ctx.push_token(ClacToken::Number(2i32.pow(trailing)))?;
                    ctx.push_token(ClacToken::Mod)?;
                    if total_shift > 0 {
                        ctx.push_token(ClacToken::Number(2i32.pow(total_shift)))?;
                        ctx.push_token(ClacToken::Mul)?;
                    }
                    ctx.push_token(ClacToken::Add)?;

                    total_shift += trailing;
                    rhs >>= trailing;
                    if rhs != 0 {
                        total_shift += rhs.trailing_zeros();
                        rhs >>= rhs.trailing_zeros();
                    } else {
                        break;
                    }
                }

                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::If {
                condition,
                on_true,
                on_false,
            } => {
                let (on_true_mangled, def_true) = ctx
                    .lookup_definition(*on_true)
                    .wrap_err_with(|| format!("Unknown if on_true definition, '{on_true:?}'"))?;

                if let Some(on_false) = on_false {
                    let (on_false_mangled, def_false) =
                        ctx.lookup_definition(*on_false).wrap_err_with(|| {
                            format!("Unknown if false_true definition, '{on_true:?}'")
                        })?;

                    assert_eq!(def_true, def_false);

                    ctx.bring_up_references(&[*condition], 1)?;
                    ctx.push_token(ClacToken::If)?;
                    ctx.push_token(ClacToken::Call {
                        mangled_ident: on_true_mangled,
                        stack_delta: def_true.stack_delta(),
                    })?;

                    let cursor_pos = ctx.cursor;

                    ctx.push_token(ClacToken::Number(1))?;
                    ctx.push_token(ClacToken::Skip)?;
                    ctx.push_token(ClacToken::Call {
                        mangled_ident: on_false_mangled,
                        stack_delta: def_false.stack_delta(),
                    })?;

                    // This avoids double counting the stack delta,
                    // We will either hit on true or on false, never both
                    // This sets the counter back to the its value after the first call
                    ctx.cursor = cursor_pos;
                } else {
                    assert_eq!(def_true.stack_delta(), 0);

                    ctx.bring_up_references(&[*condition], 1)?;
                    ctx.push_token(ClacToken::If)?;
                    ctx.push_token(ClacToken::Call {
                        mangled_ident: on_true_mangled,
                        stack_delta: def_true.stack_delta(),
                    })?;
                    ctx.push_token(ClacToken::Number(0))?;
                    ctx.push_token(ClacToken::Skip)?;
                }
            }
            ClacOp::Call { name, parameters } => {
                let (mangled, def) = ctx.lookup_definition(*name).expect("Call valid definition");
                let return_type = def.return_type;

                ctx.bring_up_references(parameters, def.paramater_width())?;
                ctx.push_token(ClacToken::Call {
                    mangled_ident: mangled,
                    stack_delta: def.stack_delta(),
                })?;

                result = Some(ctx.allocate_tempoary(return_type));
            }
        }

        Ok(result)
    }
}
