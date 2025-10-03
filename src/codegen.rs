use std::{
    collections::HashMap,
    fmt::{self, Display},
    sync::atomic::{AtomicU64, Ordering},
};

use crate::ast::{Ident, IdentRef, Type, Value};

static TEMPOARY_COUNTER: AtomicU64 = AtomicU64::new(0);
static FUNCTION_COUNTER: AtomicU64 = AtomicU64::new(0);
static STATIC_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum DefinitionIdent<'a> {
    Function(IdentRef<'a>),
    Static(IdentRef<'a>),
}
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct MangledIdent(pub Ident);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TempoaryIdent(pub u64);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct BranchIdent(pub u64);

/// Repersents an offset from bottom of the stack / start of the program
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Offset(pub u32);

#[derive(Debug, Clone)]
pub struct ScopeFrame<'a> {
    frame_start: u32,
    pub locals: HashMap<IdentRef<'a>, (Type, Offset)>,
    pub temporaries: HashMap<TempoaryIdent, (Type, Offset)>,
    pub definitions: HashMap<StoredDefinitionIdent<'a>, (MangledIdent, FunctionSignature<'a>)>,
}

#[derive(Debug, Clone)]
pub struct CodegenCtx<'a> {
    pub tokens: Vec<ClacToken<'a>>,
    pub scope_stack: Vec<ScopeFrame<'a>>,
    // Index of one past the top of the stack
    // Aka the length of the stack
    cursor: u32,
}

// FIXME: Many of these functions should be private
impl<'a> CodegenCtx<'a> {
    pub fn push_scope_frame(&mut self) -> &mut ScopeFrame<'a> {
        self.scope_stack.push_mut(ScopeFrame {
            frame_start: self.cursor,
            locals: Default::default(),
            temporaries: Default::default(),
            definitions: Default::default(),
        })
    }

    pub fn pop_scope_frame(&mut self) -> Option<ScopeFrame<'a>> {
        self.scope_stack.pop()
    }

    pub fn top_scope_frame(&mut self) -> &mut ScopeFrame<'a> {
        if self.scope_stack.is_empty() {
            self.push_scope_frame()
        } else {
            self.scope_stack.last_mut().unwrap()
        }
    }

    pub fn allocate_tempoary(&mut self, var_type: Type) -> TempoaryIdent {
        let ident = TempoaryIdent(TEMPOARY_COUNTER.fetch_add(1, Ordering::Relaxed));

        let offset = Offset(self.cursor);
        self.cursor += var_type.width();

        self.top_scope_frame()
            .temporaries
            .insert(ident, (var_type, offset));

        ident
    }

    pub fn promote_tempoary_to_local(
        &mut self,
        tempoary: TempoaryIdent,
        ident: IdentRef<'a>,
    ) -> bool {
        let Some(tempoary) = self.lookup_temporary(&tempoary) else {
            return false;
        };

        self.top_scope_frame().locals.insert(ident, tempoary);

        return true;
    }

    pub fn define_function<F: FnOnce(&mut Self)>(
        &mut self,
        ident: IdentRef<'a>,
        signature: FunctionSignature<'a>,
        scope: F,
    ) -> DefinitionIdent<'a> {
        let def_ident = DefinitionIdent::Function(ident);
        let num = FUNCTION_COUNTER.fetch_add(1, Ordering::Relaxed);

        self.push_token(ClacToken::StartDef(def_ident));

        {
            let frame = self.push_scope_frame();
            frame.frame_start -= signature.paramater_width();
            let mut offset = 0;
            frame
                .locals
                .extend(signature.arguements.iter().map(|(var_type, ident)| {
                    let cur_offset = offset;
                    offset += var_type.width();

                    (*ident, (*var_type, Offset(frame.frame_start + cur_offset)))
                }));

            (scope)(self);

            let frame = self.pop_scope_frame().unwrap();
            let needs_dropping =
                self.cursor as i32 - frame.frame_start as i32 - signature.return_width() as i32;

            assert!(needs_dropping >= 0);

            for _ in 0..needs_dropping {
                // TODO: Optimize, generalize
                if signature.return_width() > 0 {
                    assert_eq!(signature.return_width(), 1);
                    self.push_token(ClacToken::Swap);
                }
                self.push_token(ClacToken::Drop);
            }

            assert_eq!(self.cursor - frame.frame_start, signature.return_width());
        }

        self.push_token(ClacToken::EndDef);

        self.top_scope_frame().definitions.insert(
            StoredDefinitionIdent(def_ident),
            (MangledIdent(format!("func-{}-{}", ident, num)), signature),
        );

        def_ident
    }

    pub fn define_static<F: FnOnce(&mut Self)>(
        &mut self,
        ident: IdentRef<'a>,
        var_type: Type,
        value: Value,
    ) -> DefinitionIdent<'a> {
        let def_ident = DefinitionIdent::Static(ident);
        let num = STATIC_COUNTER.fetch_add(1, Ordering::Relaxed);

        self.push_token(ClacToken::StartDef(def_ident));

        {
            self.push_scope_frame();
            self.push_token(ClacToken::Number(value.as_repr()));
            self.pop_scope_frame();
        }

        self.push_token(ClacToken::EndDef);

        self.top_scope_frame().definitions.insert(
            StoredDefinitionIdent(def_ident),
            (
                MangledIdent(format!("static-{}-{}", ident, num)),
                FunctionSignature {
                    arguements: vec![],
                    return_type: var_type,
                },
            ),
        );

        def_ident
    }

    /// Copies the data pointed to by the references to the top of the stack
    /// Stack after call: S, r_1, ..., r_n
    pub fn bring_up_references(&mut self, references: &[DataReference<'a>], expected_width: u32) {
        // TODO: Optimize
        let starting_cursor = self.cursor;
        for reference in references {
            match reference {
                DataReference::Number(num) => self.push_token(ClacToken::Number(*num)),
                DataReference::Static(ident) => {
                    self.push_token(ClacToken::Call(DefinitionIdent::Static(ident)));
                }
                DataReference::Local(ident) => {
                    let (var_type, offset) =
                        self.lookup_local(ident).expect("Bring up valid local");

                    let rel_offset = self.cursor - offset.0;
                    for _ in 0..var_type.width() {
                        self.push_token(ClacToken::Number(rel_offset as i32));
                        self.push_token(ClacToken::Pick);
                    }
                }
                DataReference::Tempoary(ident) => {
                    let (var_type, offset) = self
                        .lookup_temporary(ident)
                        .expect("Bring up valid temporary");

                    let rel_offset = self.cursor - offset.0;
                    for _ in 0..var_type.width() {
                        self.push_token(ClacToken::Number(rel_offset as i32));
                        self.push_token(ClacToken::Pick);
                    }
                }
            }
        }
        assert_eq!(self.cursor - starting_cursor, expected_width)
    }

    pub fn push_token(&mut self, token: ClacToken<'a>) {
        self.cursor = (self.cursor as i32 + token.stack_delta(&self)) as u32;
        self.tokens.push(token);

        // Sanity check
        assert!(self.cursor >= self.top_scope_frame().frame_start);
    }

    pub fn lookup_definition(
        &self,
        ident: DefinitionIdent,
    ) -> Option<(&MangledIdent, &FunctionSignature<'a>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((mangled, def)) = frame.definitions.get(&ident) {
                return Some((mangled, def));
            }
        }

        None
    }

    pub fn lookup_local(&self, ident: &IdentRef) -> Option<(Type, Offset)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((var_type, offset)) = frame.locals.get(ident) {
                return Some((*var_type, *offset));
            }
        }

        None
    }

    pub fn lookup_temporary(&self, ident: &TempoaryIdent) -> Option<(Type, Offset)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((var_type, offset)) = frame.temporaries.get(ident) {
                return Some((*var_type, *offset));
            }
        }

        None
    }
}

#[derive(Debug, Clone, Copy)]
pub enum DataReference<'a> {
    Number(i32),
    Local(IdentRef<'a>),
    Static(IdentRef<'a>),
    Tempoary(TempoaryIdent),
}

#[derive(Debug, Clone, PartialEq, Eq)]
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
    pub fn append_into(&self, ctx: &mut CodegenCtx<'a>) -> Option<TempoaryIdent> {
        let mut result = None;

        match self {
            ClacOp::Print { value } => {
                ctx.bring_up_references(&[*value], 1);
                ctx.push_token(ClacToken::Print);
            }
            ClacOp::Quit => {
                ctx.push_token(ClacToken::Quit);
            }
            ClacOp::Add { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                ctx.push_token(ClacToken::Add);
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Sub { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                ctx.push_token(ClacToken::Sub);
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Mul { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                ctx.push_token(ClacToken::Mul);
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Div { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                ctx.push_token(ClacToken::Div);
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Mod { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                result = Some(ctx.allocate_tempoary(Type::Int));
                ctx.push_token(ClacToken::Mod);
            }
            ClacOp::Pow { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                ctx.push_token(ClacToken::Pow);
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Lt { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                ctx.push_token(ClacToken::Lt);
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Gt { lhs, rhs } => {
                // lhs and rhs reversed to save an instruction
                ctx.bring_up_references(&[*rhs, *lhs], 2);
                // ctx.push_token(ClacToken::Swap);
                ctx.push_token(ClacToken::Lt);
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Le { lhs, rhs } => {
                ctx.push_token(ClacToken::Number(1));
                // lhs and rhs reversed to save an instruction
                ctx.bring_up_references(&[*rhs, *lhs], 2);
                // ctx.push_token(ClacToken::Swap);
                ctx.push_token(ClacToken::Lt);
                ctx.push_token(ClacToken::Sub);
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Ge { lhs, rhs } => {
                ctx.push_token(ClacToken::Number(1));
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                ctx.push_token(ClacToken::Lt);
                ctx.push_token(ClacToken::Sub);
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Eq { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                ctx.push_token(ClacToken::Sub);
                ctx.push_token(ClacToken::If);
                ctx.push_token(ClacToken::Number(0));
                ctx.push_token(ClacToken::Number(1));
                ctx.push_token(ClacToken::Skip);
                ctx.push_token(ClacToken::Number(1));
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Ne { lhs, rhs } => {
                ctx.bring_up_references(&[*lhs, *rhs], 2);
                ctx.push_token(ClacToken::Sub);
                ctx.push_token(ClacToken::If);
                ctx.push_token(ClacToken::Number(1));
                ctx.push_token(ClacToken::Number(1));
                ctx.push_token(ClacToken::Skip);
                ctx.push_token(ClacToken::Number(0));
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::Neg { value } => {
                ctx.push_token(ClacToken::Number(0));
                ctx.bring_up_references(&[*value], 1);
                ctx.push_token(ClacToken::Sub);
                result = Some(ctx.allocate_tempoary(Type::Int));
            }
            ClacOp::Not { value } => {
                ctx.push_token(ClacToken::Number(1));
                ctx.bring_up_references(&[*value], 1);
                ctx.push_token(ClacToken::Sub);
                result = Some(ctx.allocate_tempoary(Type::Bool));
            }
            ClacOp::If {
                condition,
                on_true,
                on_false,
            } => {
                let (_mangled, def_true) = ctx
                    .lookup_definition(*on_true)
                    .expect("If valid true definition");

                if let Some(on_false) = on_false {
                    let (_mangled, def_false) = ctx
                        .lookup_definition(*on_false)
                        .expect("If valid false definition");

                    assert_eq!(def_true, def_false);

                    ctx.bring_up_references(&[*condition], 1);
                    ctx.push_token(ClacToken::If);
                    ctx.push_token(ClacToken::Call(*on_true));

                    let cursor_pos = ctx.cursor;

                    ctx.push_token(ClacToken::Number(1));
                    ctx.push_token(ClacToken::Skip);
                    ctx.push_token(ClacToken::Call(*on_false));

                    // This avoids double counting the stack delta,
                    // We will either hit on true or on false, never both
                    ctx.cursor = cursor_pos;
                } else {
                    assert_eq!(def_true.stack_delta(), 0);

                    ctx.bring_up_references(&[*condition], 1);
                    ctx.push_token(ClacToken::If);
                    ctx.push_token(ClacToken::Call(*on_true));
                    ctx.push_token(ClacToken::Number(0));
                    ctx.push_token(ClacToken::Skip);
                }
            }
            ClacOp::Call { name, parameters } => {
                let (_mangled, def) = ctx.lookup_definition(*name).expect("Call valid definition");
                let return_type = def.return_type;

                ctx.bring_up_references(&parameters, def.paramater_width());
                ctx.push_token(ClacToken::Call(*name));

                result = Some(ctx.allocate_tempoary(return_type));
            }
        }

        return result;
    }
}

/// A Clac Source Code Token
#[derive(Debug, Clone)]
pub enum ClacToken<'a> {
    Number(i32),
    Print,
    Quit,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Pow,
    Lt,
    Drop,
    Swap,
    Rot,
    If,
    Pick,
    Skip,
    StartDef(DefinitionIdent<'a>),
    EndDef,
    Call(DefinitionIdent<'a>),
}

impl ClacToken<'_> {
    pub fn stack_delta(&self, ctx: &CodegenCtx) -> i32 {
        match self {
            ClacToken::Number(_) => 1,
            ClacToken::Print => -1,
            ClacToken::Quit => 0,
            ClacToken::Add => -1,
            ClacToken::Sub => -1,
            ClacToken::Mul => -1,
            ClacToken::Div => -1,
            ClacToken::Mod => -1,
            ClacToken::Pow => -1,
            ClacToken::Lt => -1,
            ClacToken::Drop => -1,
            ClacToken::Swap => 0,
            ClacToken::Rot => 0,
            ClacToken::If => -1,
            ClacToken::Pick => 0,
            ClacToken::Skip => -1,
            ClacToken::StartDef(_) => 0,
            ClacToken::EndDef => 0,
            ClacToken::Call(ident) => {
                let (_, def) = ctx
                    .lookup_definition(*ident)
                    .expect("Token with invalid definition ident");

                def.stack_delta()
            }
        }
    }

    pub fn write(&self, ctx: &CodegenCtx, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ClacToken::Number(num) => write!(f, "{num} "),
            ClacToken::Print => write!(f, "print "),
            ClacToken::Quit => write!(f, "quit "),
            ClacToken::Add => write!(f, "+ "),
            ClacToken::Sub => write!(f, "- "),
            ClacToken::Mul => write!(f, "* "),
            ClacToken::Div => write!(f, "/ "),
            ClacToken::Mod => write!(f, "% "),
            ClacToken::Pow => write!(f, "** "),
            ClacToken::Lt => write!(f, "< "),
            ClacToken::Drop => write!(f, "drop "),
            ClacToken::Swap => write!(f, "swap "),
            ClacToken::Rot => write!(f, "rot "),
            ClacToken::If => write!(f, "if "),
            ClacToken::Pick => write!(f, "pick "),
            ClacToken::Skip => write!(f, "skip "),
            ClacToken::StartDef(ident) => {
                let (mangled, _) = ctx
                    .lookup_definition(*ident)
                    .expect("Token with invalid definition ident");

                write!(f, ": {} ", mangled.0)
            }
            ClacToken::EndDef => write!(f, "; "),
            ClacToken::Call(ident) => {
                let (mangled, _) = ctx
                    .lookup_definition(*ident)
                    .expect("Token with invalid definition ident");

                write!(f, "{} ", mangled.0)
            }
        }
    }
}

// Work arround for a lifetime issue
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub struct StoredDefinitionIdent<'a>(pub DefinitionIdent<'a>);

impl<'a: 'b, 'b> std::borrow::Borrow<DefinitionIdent<'b>> for StoredDefinitionIdent<'a> {
    fn borrow(&self) -> &DefinitionIdent<'b> {
        &self.0
    }
}
