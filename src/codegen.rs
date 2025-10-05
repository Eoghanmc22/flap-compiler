pub mod builtins;
pub mod clac;
pub mod ir;
pub mod post_process;

use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, bail, eyre},
};
use pest::Span;

use std::{
    collections::{HashMap, HashSet},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use crate::{
    ast::{FunctionAttribute, IdentRef, Type, Value},
    codegen::{
        builtins::clac_builtins,
        clac::{ClacProgram, ClacToken, MangledIdent},
        ir::{ClacOp, DataReference, FunctionSignature},
    },
    middleware::generate_span_error_section,
};

static TEMPOARY_COUNTER: AtomicU64 = AtomicU64::new(0);
static FUNCTION_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum DefinitionIdent<'a> {
    Function(IdentRef<'a>),
    Inline(IdentRef<'a>),
    Const(IdentRef<'a>),
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TempoaryIdent(pub u64);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct BranchIdent(pub u64);

/// Repersents an offset from bottom of the stack / start of the program
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Offset(pub i32);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
/// Specifies if we are allowed to access locals below this stack frame
pub enum Opaque {
    /// Allow references to locals below this frame
    AllowCaptures,
    /// Only allow references to locals in and above this frame
    Opaque,
}

pub enum MaybeTailCall<'a> {
    Regular(DataReference<'a>),
    TailCall {
        parameters: Vec<DataReference<'a>>,
        signature: Arc<FunctionSignature<'a>>,
        tokens: Arc<Vec<ClacToken>>,
        call_span: Span<'a>,
    },
}

impl<'a> MaybeTailCall<'a> {
    pub fn into_data_ref(self, ctx: &mut CodegenCtx<'a>) -> Result<DataReference<'a>> {
        match self {
            MaybeTailCall::Regular(data_reference) => Ok(data_reference),
            MaybeTailCall::TailCall {
                parameters,
                signature,
                tokens,
                call_span,
            } => {
                let res: Result<_> = try {
                    ctx.bring_up_references(&parameters, signature.paramater_width())?;

                    for token in tokens.iter() {
                        ctx.push_token(token.clone())?;
                    }

                    DataReference::Tempoary(ctx.allocate_tempoary(signature.return_type))
                };
                res.wrap_err("Error running tail call")
                    .with_section(|| generate_span_error_section(call_span))
            }
        }
    }
}

impl<'a> From<DataReference<'a>> for MaybeTailCall<'a> {
    fn from(value: DataReference<'a>) -> Self {
        MaybeTailCall::Regular(value)
    }
}

#[derive(Debug, Clone)]
pub struct ScopeFrame<'a> {
    frame_start: i32,
    locals: HashMap<IdentRef<'a>, (Type, DataReference<'a>)>,
    temporaries: HashMap<TempoaryIdent, (Type, Offset)>,
    definitions: HashMap<StoredDefinitionIdent<'a>, (ClacToken, Arc<FunctionSignature<'a>>)>,

    opaque: Opaque,
    allow_underflow: bool,
}

#[derive(Debug, Clone)]
pub struct CodegenCtx<'a> {
    tokens: Vec<ClacToken>,
    scope_stack: Vec<ScopeFrame<'a>>,
    // Index of one past the top of the stack
    // Aka the length of the stack
    cursor: i32,
}

impl Default for CodegenCtx<'_> {
    fn default() -> Self {
        let mut ctx = Self {
            tokens: Default::default(),
            scope_stack: Default::default(),
            cursor: Default::default(),
        };

        ctx.define_function(
            "drop_range",
            FunctionSignature {
                arguements: vec![(Type::Int, "start_depth"), (Type::Int, "end_depth")],
                return_type: Type::Void,
            },
            &[
                FunctionAttribute::NoMangle,
                FunctionAttribute::AllowUnderflow,
                FunctionAttribute::Naked,
            ]
            .into(),
            |ctx| {
                ctx.define_function(
                    "drop_range_outer",
                    FunctionSignature {
                        arguements: vec![(Type::Int, "start_depth"), (Type::Int, "end_depth")],
                        return_type: Type::Void,
                    },
                    &[
                        FunctionAttribute::NoMangle,
                        FunctionAttribute::AllowUnderflow,
                        FunctionAttribute::Naked,
                    ]
                    .into(),
                    |ctx| {
                        ctx.define_function(
                            "drop_range_inner",
                            FunctionSignature {
                                arguements: vec![
                                    (Type::Int, "start_depth"),
                                    (Type::Int, "end_depth"),
                                    (Type::Int, "number"),
                                ],
                                return_type: Type::Void,
                            },
                            &[
                                FunctionAttribute::NoMangle,
                                FunctionAttribute::AllowUnderflow,
                                FunctionAttribute::Naked,
                            ]
                            .into(),
                            |ctx| {
                                // Debug
                                ctx.push_token(ClacToken::Number(99999999))?;
                                ctx.push_token(ClacToken::Print)?;
                                ctx.push_token(ClacToken::Number(1))?;
                                ctx.push_token(ClacToken::Pick)?;
                                ctx.push_token(ClacToken::Print)?;
                                ctx.push_token(ClacToken::Number(2))?;
                                ctx.push_token(ClacToken::Pick)?;
                                ctx.push_token(ClacToken::Print)?;
                                ctx.push_token(ClacToken::Number(3))?;
                                ctx.push_token(ClacToken::Pick)?;
                                ctx.push_token(ClacToken::Print)?;

                                // start, end, num

                                // Load number
                                ctx.push_token(ClacToken::Number(1))?;
                                ctx.push_token(ClacToken::Pick)?;

                                // Load number
                                ctx.push_token(ClacToken::Number(2))?;
                                ctx.push_token(ClacToken::Pick)?;

                                // start, end, num, num, num

                                // if number != 0
                                ctx.push_token(ClacToken::If)?;
                                // start, end, num, num
                                // later used for mod
                                ctx.push_token(ClacToken::Number(2))?;
                                ctx.push_token(ClacToken::Number(12))?;
                                ctx.push_token(ClacToken::Skip)?;

                                // if number == 0
                                // start, end, num, num
                                ctx.push_token(ClacToken::Drop)?;
                                ctx.push_token(ClacToken::Drop)?;
                                ctx.push_token(ClacToken::Number(-1))?;
                                ctx.push_token(ClacToken::Add)?;
                                ctx.push_token(ClacToken::Swap)?;
                                ctx.push_token(ClacToken::Number(-1))?;
                                ctx.push_token(ClacToken::Add)?;
                                ctx.push_token(ClacToken::Swap)?;
                                // start-1, end-1
                                ctx.push_token(ClacToken::Call {
                                    mangled_ident: MangledIdent(
                                        "drop_range_outer".to_string().into(),
                                    ),
                                    stack_delta: 0,
                                })?;
                                // Base case for reconstruction
                                ctx.push_token(ClacToken::Number(0))?;
                                ctx.push_token(ClacToken::Number(18))?;
                                ctx.push_token(ClacToken::Skip)?;

                                // if number != 0
                                // start_depth, end_depth, number, number, 2
                                {
                                    // number % 2 = lsb(number)
                                    ctx.push_token(ClacToken::Mod)?;

                                    // number, number%2
                                    ctx.push_token(ClacToken::Swap)?;

                                    // number%2, number
                                    ctx.push_token(ClacToken::Number(2))?;
                                    ctx.push_token(ClacToken::Div)?;

                                    // number%2, number/2
                                    ctx.push_token(ClacToken::Swap)?;
                                    // number/2, number%2

                                    // if lsb(number) == 1
                                    ctx.push_token(ClacToken::If)?;
                                    // start_depth, end_depth, number/2
                                    ctx.push_token(ClacToken::Call {
                                        mangled_ident: MangledIdent(
                                            "drop_range_inner".to_string().into(),
                                        ),
                                        stack_delta: 0,
                                    })?;
                                    ctx.push_token(ClacToken::Number(4))?;
                                    ctx.push_token(ClacToken::Skip)?;

                                    // if lsb(number) == 0
                                    // start_depth, end_depth, number/2
                                    ctx.push_token(ClacToken::Call {
                                        mangled_ident: MangledIdent(
                                            "drop_range_inner".to_string().into(),
                                        ),
                                        stack_delta: 0,
                                    })?;
                                    ctx.push_token(ClacToken::Number(0))?;
                                    ctx.push_token(ClacToken::Number(1))?;
                                    ctx.push_token(ClacToken::Skip)?;

                                    // if lsb(number) == 1
                                    ctx.push_token(ClacToken::Number(1))?;

                                    // start_depth, end_depth, number/2, lsb(number)
                                    ctx.push_token(ClacToken::Swap)?;
                                    ctx.push_token(ClacToken::Number(2))?;
                                    ctx.push_token(ClacToken::Mul)?;
                                    ctx.push_token(ClacToken::Add)?;
                                    // start_depth, end_depth, number
                                }

                                Ok(MaybeTailCall::Regular(DataReference::Tempoary(
                                    ctx.allocate_tempoary(Type::Void),
                                )))
                            },
                        )
                        .wrap_err("Define builtin drop_range_inner")?;

                        // Debug
                        ctx.push_token(ClacToken::Number(7777777))?;
                        ctx.push_token(ClacToken::Print)?;
                        ctx.push_token(ClacToken::Number(1))?;
                        ctx.push_token(ClacToken::Pick)?;
                        ctx.push_token(ClacToken::Print)?;
                        ctx.push_token(ClacToken::Number(2))?;
                        ctx.push_token(ClacToken::Pick)?;
                        ctx.push_token(ClacToken::Print)?;

                        // Initial value for drop_range_inner `number`
                        ctx.push_token(ClacToken::Rot)?;

                        // start, end, number

                        // Load start depth
                        ctx.push_token(ClacToken::Number(3))?;
                        ctx.push_token(ClacToken::Pick)?;

                        // start, end, number, start

                        // if start_depth != 0
                        ctx.push_token(ClacToken::If)?;
                        ctx.push_token(ClacToken::Call {
                            mangled_ident: MangledIdent("drop_range_inner".to_string().into()),
                            stack_delta: 0,
                        })?;
                        // start, end, number_reconstructed
                        ctx.push_token(ClacToken::Number(0))?;
                        ctx.push_token(ClacToken::Skip)?;

                        // start, end, number_to_drop or number_reconstructed

                        // Load end depth
                        ctx.push_token(ClacToken::Number(2))?;
                        ctx.push_token(ClacToken::Pick)?;

                        // start, end, number_to_drop or number_reconstructed, end
                        // DEBUG
                        ctx.push_token(ClacToken::Number(1))?;
                        ctx.push_token(ClacToken::Pick)?;
                        ctx.push_token(ClacToken::Print)?;

                        // if end_depth != 0
                        ctx.push_token(ClacToken::If)?;
                        ctx.push_token(ClacToken::Drop)?;
                        ctx.push_token(ClacToken::Number(4))?;
                        ctx.push_token(ClacToken::Skip)?;

                        // if end_depth == 0
                        ctx.push_token(ClacToken::Rot)?;
                        ctx.push_token(ClacToken::Rot)?;
                        ctx.push_token(ClacToken::Number(3))?;
                        ctx.push_token(ClacToken::Skip)?;

                        // if end_depth != 0
                        // start, end
                        ctx.push_token(ClacToken::Number(-1))?;
                        ctx.push_token(ClacToken::Add)?;
                        ctx.push_token(ClacToken::Call {
                            mangled_ident: MangledIdent("drop_range_outer".to_string().into()),
                            stack_delta: 0,
                        })?;

                        Ok(MaybeTailCall::Regular(DataReference::Tempoary(
                            ctx.allocate_tempoary(Type::Void),
                        )))
                    },
                )
                .wrap_err("Define builtin drop_range_outer")
                .unwrap();

                ctx.push_token(ClacToken::Call {
                    mangled_ident: MangledIdent("drop_range_outer".to_string().into()),
                    stack_delta: 0,
                })?;
                ctx.push_token(ClacToken::Drop)?;
                ctx.push_token(ClacToken::Drop)?;

                // DEBUG
                ctx.push_token(ClacToken::Number(1000))?;
                ctx.push_token(ClacToken::Skip)?;

                Ok(MaybeTailCall::Regular(DataReference::Tempoary(
                    ctx.allocate_tempoary(Type::Void),
                )))
            },
        )
        .wrap_err("Define builtin drop_range")
        .unwrap();

        for (ident, (code, sig)) in clac_builtins() {
            ctx.define_inline(&ident, sig, code);
        }

        // Allocates the first stack frame
        // Necessary to gurantee that the first stack frame starts at 0
        ctx.top_scope_frame();

        ctx
    }
}

// FIXME: Many of these functions should be private
impl<'a> CodegenCtx<'a> {
    pub fn into_tokens(self) -> ClacProgram {
        ClacProgram(self.tokens)
    }

    fn push_scope_frame(&mut self, attributes: &HashSet<FunctionAttribute>) -> &mut ScopeFrame<'a> {
        self.scope_stack.push_mut(ScopeFrame {
            frame_start: self.cursor,
            locals: Default::default(),
            temporaries: Default::default(),
            definitions: Default::default(),
            opaque: if attributes.contains(&FunctionAttribute::AllowCaptures) {
                Opaque::AllowCaptures
            } else {
                Opaque::Opaque
            },
            allow_underflow: attributes.contains(&FunctionAttribute::AllowUnderflow),
        })
    }

    fn pop_scope_frame(&mut self) -> Option<ScopeFrame<'a>> {
        self.scope_stack.pop()
    }

    fn top_scope_frame(&mut self) -> &mut ScopeFrame<'a> {
        if self.scope_stack.is_empty() {
            self.push_scope_frame(&Default::default())
        } else {
            self.scope_stack.last_mut().unwrap()
        }
    }

    pub fn allocate_tempoary(&mut self, var_type: Type) -> TempoaryIdent {
        let ident = TempoaryIdent(TEMPOARY_COUNTER.fetch_add(1, Ordering::Relaxed));

        assert!(var_type == Type::Void || self.cursor > 0);
        let offset = Offset(self.cursor - 1);

        self.top_scope_frame()
            .temporaries
            .insert(ident, (var_type, offset));

        ident
    }

    pub fn promote_to_local(
        &mut self,
        data_ref: DataReference<'a>,
        ident: IdentRef<'a>,
        var_type: Type,
    ) {
        self.top_scope_frame()
            .locals
            .insert(ident, (var_type, data_ref));
    }

    pub fn define_function<F: FnOnce(&mut Self) -> Result<MaybeTailCall<'a>>>(
        &mut self,
        ident: IdentRef<'a>,
        signature: FunctionSignature<'a>,
        attributes: &HashSet<FunctionAttribute>,
        scope: F,
    ) -> Result<DefinitionIdent<'a>> {
        let def_ident = DefinitionIdent::Function(ident);
        let num = FUNCTION_COUNTER.fetch_add(1, Ordering::Relaxed);

        let mangled = if attributes.contains(&FunctionAttribute::NoMangle) {
            ident.to_string()
        } else {
            format!("func-{}-{}", ident, num)
        };
        let mangled = MangledIdent(Arc::new(mangled));

        let signature = Arc::new(signature);

        self.top_scope_frame().definitions.insert(
            StoredDefinitionIdent(def_ident),
            (
                ClacToken::Call {
                    mangled_ident: mangled.clone(),
                    stack_delta: signature.stack_delta(),
                },
                signature.clone(),
            ),
        );

        let original_cursor = self.cursor;
        self.push_token(ClacToken::StartDef {
            mangled_ident: mangled,
        })
        .unwrap();

        {
            self.push_scope_frame(&attributes);
            self.cursor += signature.paramater_width() as i32;

            let frame = self.top_scope_frame();
            println!("New Frame 1 '{ident}': {frame:#?}");

            let mut offset = 0;
            for (var_type, ident) in &signature.arguements {
                let cur_offset = Offset(frame.frame_start + offset);
                offset += var_type.width() as i32;

                // Name arg as a tempoary
                let tempoary = TempoaryIdent(TEMPOARY_COUNTER.fetch_add(1, Ordering::Relaxed));
                frame.temporaries.insert(tempoary, (*var_type, cur_offset));
                frame
                    .locals
                    .insert(ident, (*var_type, DataReference::Tempoary(tempoary)));
            }
            println!("New Frame 1 '{ident}': {frame:#?}");

            let return_data_ref = (scope)(self)?;

            let (retain_width, tail_call) = match return_data_ref {
                MaybeTailCall::Regular(data_reference) => {
                    self.bring_up_references(&[data_reference], signature.return_width())?;

                    (signature.return_width(), None)
                }
                MaybeTailCall::TailCall {
                    parameters,
                    signature: tail_call_sig,
                    tokens,
                    call_span,
                } => {
                    if signature.return_type != tail_call_sig.return_type {
                        return Err(eyre!(
                            "Attempted to tail call `{ident}` but it returns a {:?}, and the calling runction returns a {:?}",
                            tail_call_sig.return_type,
                            signature.return_type
                        )).with_section(|| generate_span_error_section(call_span));
                    }

                    self.bring_up_references(&parameters, tail_call_sig.paramater_width())
                        .wrap_err("COMPILER BUG: error bringing up references for tail call")
                        .with_section(|| generate_span_error_section(call_span))?;

                    (tail_call_sig.paramater_width(), Some(tokens))
                }
            };

            if !attributes.contains(&FunctionAttribute::Naked) {
                let frame = self.pop_scope_frame().unwrap();
                let needs_dropping = self.cursor - frame.frame_start - retain_width as i32;

                assert!(needs_dropping >= 0);

                for _ in 0..needs_dropping {
                    // TODO: Optimize, generalize
                    if retain_width > 0 {
                        assert_eq!(retain_width, 1);
                        self.push_token(ClacToken::Swap)?;
                    }
                    self.push_token(ClacToken::Drop)?;
                }

                assert_eq!(self.cursor - frame.frame_start, retain_width as i32);
            }

            if let Some(tail_call) = tail_call {
                for token in tail_call.iter() {
                    self.push_token(token.clone())?;
                }
            }
        }

        self.push_token(ClacToken::EndDef)?;
        self.cursor = original_cursor;

        Ok(def_ident)
    }

    pub fn define_const(
        &mut self,
        ident: IdentRef<'a>,
        var_type: Type,
        value: Value,
    ) -> Result<DefinitionIdent<'a>> {
        let def_ident = DefinitionIdent::Const(ident);

        let signature = Arc::new(FunctionSignature {
            arguements: vec![],
            return_type: var_type,
        });

        self.top_scope_frame().definitions.insert(
            StoredDefinitionIdent(def_ident),
            (ClacToken::Number(value.as_repr()), signature),
        );

        Ok(def_ident)
    }

    pub fn define_inline(
        &mut self,
        ident: IdentRef<'a>,
        sig: FunctionSignature<'a>,
        token: ClacToken,
    ) -> DefinitionIdent<'a> {
        let def_ident = DefinitionIdent::Inline(ident);

        self.top_scope_frame()
            .definitions
            .insert(StoredDefinitionIdent(def_ident), (token, Arc::new(sig)));

        def_ident
    }

    /// Copies the data pointed to by the references to the top of the stack
    /// Stack after call: S, r_1, ..., r_n
    // TODO: Check types instead of widths
    pub fn bring_up_references(
        &mut self,
        references: &[DataReference<'a>],
        expected_width: u32,
    ) -> Result<()> {
        println!("bring up references '{references:?}', expected_width, {expected_width}");

        // TODO: Optimize
        let starting_cursor = self.cursor;
        for reference in references {
            println!("bring up reference '{reference:?}'",);

            match *reference {
                DataReference::Number(num) => self.push_token(ClacToken::Number(num))?,
                DataReference::Const(ident) => {
                    let (func_impl, sig) = self
                        .lookup_definition(DefinitionIdent::Const(ident))
                        .wrap_err("Bring up valid const")?;

                    if !sig.arguements.is_empty() {
                        bail!("Constant '{ident}' has a non zero number of arguements: {sig:?}");
                    }

                    self.push_token(func_impl)?;
                }
                DataReference::Local(ident) => {
                    let (var_type, data_ref) =
                        self.lookup_local(ident).wrap_err("Bring up valid local")?;

                    println!("recursing to bring up local reference '{ident}'",);
                    self.bring_up_references(&[data_ref], var_type.width())?;
                }
                DataReference::Tempoary(ident) => {
                    let (var_type, offset) = self
                        .lookup_temporary(ident)
                        .expect("Bring up valid temporary");

                    if var_type == Type::Void {
                        continue;
                    }

                    let rel_offset = self.cursor - offset.0;
                    println!(
                        "bring up reference '{reference:?}', cursor: {}, offset: {}, rel_offset: {}",
                        self.cursor, offset.0, rel_offset
                    );
                    for _ in 0..var_type.width() {
                        if rel_offset <= 0 {
                            bail!("Got rel_offset {rel_offset} < 0");
                        }
                        self.push_token(ClacToken::Number(rel_offset))?;
                        self.push_token(ClacToken::Pick)?;
                    }
                }
            }
        }

        if self.cursor - starting_cursor != expected_width as i32 {
            bail!(
                "Type error?: expected to load width {expected_width}, actually loaded: {}, references: {references:#?}",
                self.cursor - starting_cursor
            )
        }

        Ok(())
    }

    pub fn push_token(&mut self, token: ClacToken) -> Result<()> {
        self.cursor += token.stack_delta();

        if !self.top_scope_frame().allow_underflow {
            // Sanity check
            assert!(
                self.cursor >= self.top_scope_frame().frame_start,
                "COMPILER BUG: underflowed stack frame on token `{token:?}`"
            );
        }

        self.tokens.push(token);

        Ok(())
    }

    pub fn call_function_like(
        &mut self,
        ident: IdentRef<'a>,
        parameters: Vec<DataReference<'a>>,
        call_span: Span<'a>,
    ) -> Result<MaybeTailCall<'a>> {
        let (func_impl, sig) = self
            .lookup_function_like_signature(ident)
            .wrap_err("Attempted to call unknown function-like")
            .with_section(|| generate_span_error_section(call_span))?;

        Ok(MaybeTailCall::TailCall {
            parameters,
            signature: sig,
            tokens: Arc::new(vec![func_impl]),
            call_span,
        })
    }

    pub fn lookup_function_like_signature(
        &self,
        ident: IdentRef<'a>,
    ) -> Option<(ClacToken, Arc<FunctionSignature<'a>>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((func_impl, sig)) = frame.definitions.get(&DefinitionIdent::Inline(ident)) {
                return Some((func_impl.clone(), sig.clone()));
            }
            if let Some((func_impl, sig)) = frame.definitions.get(&DefinitionIdent::Function(ident))
            {
                return Some((func_impl.clone(), sig.clone()));
            }
        }

        None
    }

    pub fn lookup_definition(
        &self,
        ident: DefinitionIdent,
    ) -> Option<(ClacToken, Arc<FunctionSignature<'a>>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((func_impl, sig)) = frame.definitions.get(&ident) {
                return Some((func_impl.clone(), sig.clone()));
            }
        }

        None
    }

    pub fn lookup_local(&self, ident: IdentRef) -> Option<(Type, DataReference<'a>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((var_type, data_ref)) = frame.locals.get(ident) {
                return Some((*var_type, *data_ref));
            }
            if frame.opaque == Opaque::Opaque {
                break;
            }
        }

        None
    }

    pub fn lookup_temporary(&self, ident: TempoaryIdent) -> Option<(Type, Offset)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((var_type, offset)) = frame.temporaries.get(&ident) {
                return Some((*var_type, *offset));
            }
        }

        None
    }

    pub fn lookup_ident_data_ref(&self, ident: IdentRef<'a>) -> Option<(DataReference<'a>, Type)> {
        let mut is_opaque = false;

        for frame in self.scope_stack.iter().rev() {
            if !is_opaque {
                if let Some((var_type, _)) = frame.locals.get(ident) {
                    return Some((DataReference::Local(ident), *var_type));
                }
            }

            if let Some((_, sig)) = frame.definitions.get(&DefinitionIdent::Const(ident)) {
                return Some((DataReference::Const(ident), sig.return_type));
            }

            is_opaque |= frame.opaque == Opaque::Opaque;
        }

        None
    }
}

// Work arround for a lifetime issue
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct StoredDefinitionIdent<'a>(pub DefinitionIdent<'a>);

impl<'a: 'b, 'b> std::borrow::Borrow<DefinitionIdent<'b>> for StoredDefinitionIdent<'a> {
    fn borrow(&self) -> &DefinitionIdent<'b> {
        &self.0
    }
}
