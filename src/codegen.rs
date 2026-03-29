pub mod builtins;
pub mod clac;
pub mod ir;
pub mod post_process;

use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, Result, bail, eyre},
};
use pest::Span;
use tracing::{debug, instrument, trace};

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
        clac::{ClacProgram, ClacToken, ClacValue, MangledIdent},
        ir::{DataReference, FunctionSignature},
    },
    middleware::generate_span_error_section,
};

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
pub struct Offset(pub ClacValue);

#[derive(Debug, Clone)]
pub struct AnnotatedDataRef<'a> {
    pub reference: DataReference<'a>,
    pub data_type: Type,
}

#[derive(Debug, Clone)]
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
    #[instrument(skip(ctx))]
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

                    DataReference::Tempoary(ctx.allocate_tempoary(signature.return_type.clone()))
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
    frame_start: ClacValue,
    locals: HashMap<IdentRef<'a>, AnnotatedDataRef<'a>>,
    temporaries: HashMap<TempoaryIdent, (Type, Offset)>,
    definitions: HashMap<StoredDefinitionIdent<'a>, (Vec<ClacToken>, Arc<FunctionSignature<'a>>)>,

    allow_underflow: bool,
}

#[derive(Debug, Clone)]
pub struct CodegenCtx<'a> {
    tokens: Vec<ClacToken>,
    scope_stack: Vec<ScopeFrame<'a>>,
    // Index of one past the top of the stack
    // Aka the length of the stack
    cursor: ClacValue,

    id_counter: Arc<AtomicU64>,
}

impl Default for CodegenCtx<'_> {
    fn default() -> Self {
        let mut ctx = Self {
            tokens: Default::default(),
            scope_stack: Default::default(),
            cursor: Default::default(),
            id_counter: Arc::new(AtomicU64::new(0)),
        };

        for (ident, (code, sig)) in clac_builtins() {
            ctx.define_inline(&ident, sig, vec![code]);
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
        let ident = TempoaryIdent(self.id_counter.fetch_add(1, Ordering::Relaxed));

        assert!(self.cursor > var_type.width());
        let offset = Offset(self.cursor - var_type.width());

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
        self.top_scope_frame().locals.insert(
            ident,
            AnnotatedDataRef {
                reference: data_ref,
                data_type: var_type,
            },
        );
    }

    #[instrument(skip(self, scope))]
    pub fn define_function<F: FnOnce(&mut Self) -> Result<MaybeTailCall<'a>>>(
        &mut self,
        ident: IdentRef<'a>,
        signature: FunctionSignature<'a>,
        attributes: &HashSet<FunctionAttribute>,
        scope: F,
    ) -> Result<DefinitionIdent<'a>> {
        let def_ident = DefinitionIdent::Function(ident);
        let num = self.id_counter.fetch_add(1, Ordering::Relaxed);

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
                vec![ClacToken::Call {
                    mangled_ident: mangled.clone(),
                    stack_delta: signature.stack_delta(),
                }],
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
            self.cursor += signature.paramater_width();

            let id_counter = self.id_counter.clone();
            let frame = self.top_scope_frame();
            let mut offset = 0;
            for (var_type, ident) in &signature.arguements {
                let cur_offset = Offset(frame.frame_start + offset);
                offset += var_type.width();

                // Name arg as a tempoary
                let tempoary = TempoaryIdent(id_counter.fetch_add(1, Ordering::Relaxed));
                frame
                    .temporaries
                    .insert(tempoary, (var_type.clone(), cur_offset));
                assert!(
                    frame
                        .locals
                        .insert(
                            ident,
                            AnnotatedDataRef {
                                reference: DataReference::Tempoary(tempoary),
                                data_type: var_type.clone(),
                            },
                        )
                        .is_none(),
                    "Dupliate function arguements"
                );
            }

            debug!("Start function frame '{ident}': {frame:#?}");

            let return_data_ref = (scope)(self)?;

            let (retain_width, tail_call) = match return_data_ref {
                MaybeTailCall::Regular(data_reference) => {
                    self.bring_up_references(&[data_reference], signature.return_width())?;

                    (signature.return_width(), None)
                }
                // MaybeTailCall::TailCall {
                //     signature: ref tail_call_sig,
                //     ..
                // } if tail_call_sig.paramater_width() > 2 => {
                //     let ret_width = tail_call_sig.return_width();
                //     let _data_ref = return_data_ref.into_data_ref(self)?;
                //     (ret_width, None)
                // }
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
                let needs_dropping = self.cursor - frame.frame_start - retain_width;

                assert!(needs_dropping >= 0);

                if retain_width == 0 && needs_dropping <= 3 {
                    for _ in 0..needs_dropping {
                        self.push_token(ClacToken::Drop)?;
                    }
                } else if retain_width == 1 && needs_dropping <= 1 {
                    for _ in 0..needs_dropping {
                        self.push_token(ClacToken::Swap)?;
                        self.push_token(ClacToken::Drop)?;
                    }
                } else if retain_width == 2 && needs_dropping <= 1 {
                    for _ in 0..needs_dropping {
                        self.push_token(ClacToken::Rot)?;
                        self.push_token(ClacToken::Drop)?;
                    }
                } else if needs_dropping > 0 {
                    self.push_token(ClacToken::Number(needs_dropping + retain_width))?;
                    self.push_token(ClacToken::Number(needs_dropping))?;
                    self.push_token(ClacToken::Call {
                        mangled_ident: MangledIdent(Arc::new("drop_range".to_string())),
                        stack_delta: -needs_dropping - 2,
                    })?;
                }

                assert_eq!(self.cursor - frame.frame_start, retain_width);
            }

            if let Some(tail_call) = tail_call {
                for token in tail_call.iter() {
                    self.push_token(token.clone())?;
                }
            }
        }

        self.push_token(ClacToken::EndDef)?;
        self.cursor = original_cursor;

        debug!("End function frame '{ident}'");

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
            (
                value.as_repr().into_iter().map(ClacToken::Number).collect(),
                signature,
            ),
        );

        Ok(def_ident)
    }

    pub fn define_inline(
        &mut self,
        ident: IdentRef<'a>,
        sig: FunctionSignature<'a>,
        tokens: Vec<ClacToken>,
    ) -> DefinitionIdent<'a> {
        let def_ident = DefinitionIdent::Inline(ident);

        self.top_scope_frame()
            .definitions
            .insert(StoredDefinitionIdent(def_ident), (tokens, Arc::new(sig)));

        def_ident
    }

    /// Copies the data pointed to by the references to the top of the stack
    /// Stack after call: S, r_1, ..., r_n
    // TODO: Check types instead of widths
    #[instrument(skip(self))]
    pub fn bring_up_references(
        &mut self,
        references: &[DataReference<'a>],
        expected_width: ClacValue,
    ) -> Result<()> {
        trace!("bring up references '{references:?}', expected_width, {expected_width}");

        // TODO: Optimize
        let starting_cursor = self.cursor;
        for reference in references {
            trace!("bring up reference '{reference:?}'",);

            match *reference {
                DataReference::Number(num) => self.push_token(ClacToken::Number(num))?,
                DataReference::Const(ident) => {
                    let (func_impl, sig) = self
                        .lookup_definition(DefinitionIdent::Const(ident))
                        .wrap_err("Bring up valid const")?;

                    if !sig.arguements.is_empty() {
                        bail!("Constant '{ident}' has a non zero number of arguements: {sig:?}");
                    }

                    for token in func_impl.to_vec() {
                        self.push_token(token)?;
                    }
                }
                DataReference::Local(ident) => {
                    let AnnotatedDataRef {
                        reference,
                        data_type,
                    } = self.lookup_local(ident).wrap_err("Bring up valid local")?;

                    trace!("recursing to bring up local reference '{ident}'",);
                    self.bring_up_references(&[reference], data_type.width())?;
                }
                DataReference::Tempoary(ident) => {
                    let (var_type, offset) = self
                        .lookup_temporary(ident)
                        .expect("Bring up valid temporary");

                    if var_type == Type::Void {
                        continue;
                    }

                    let rel_offset = self.cursor - offset.0;
                    trace!(
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

        if self.cursor - starting_cursor != expected_width {
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

    #[instrument(skip(self))]
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
            tokens: Arc::new(func_impl.to_vec()),
            call_span,
        })
    }

    pub fn lookup_function_like_signature(
        &self,
        ident: IdentRef<'a>,
    ) -> Option<(Vec<ClacToken>, Arc<FunctionSignature<'a>>)> {
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
        ident: DefinitionIdent<'a>,
    ) -> Option<(Vec<ClacToken>, Arc<FunctionSignature<'a>>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((func_impl, sig)) = frame.definitions.get(&ident) {
                return Some((func_impl.clone(), sig.clone()));
            }
        }

        None
    }

    pub fn lookup_local(&self, ident: IdentRef<'a>) -> Option<AnnotatedDataRef<'a>> {
        self.scope_stack
            .last()
            .and_then(|it| it.locals.get(ident))
            .cloned()
    }

    pub fn lookup_temporary(&self, ident: TempoaryIdent) -> Option<(Type, Offset)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((var_type, offset)) = frame.temporaries.get(&ident) {
                return Some((var_type.clone(), *offset));
            }
        }

        None
    }

    pub fn lookup_ident_data_ref(&self, ident: IdentRef<'a>) -> Option<AnnotatedDataRef<'a>> {
        if let Some(local) = self.lookup_local(ident) {
            Some(local)
        } else {
            for frame in self.scope_stack.iter().rev() {
                if let Some((_, sig)) = frame.definitions.get(&DefinitionIdent::Const(ident)) {
                    return Some(AnnotatedDataRef {
                        reference: DataReference::Const(ident),
                        data_type: sig.return_type.clone(),
                    });
                }
            }

            None
        }
    }

    pub fn dereference_data_ref(&self, data_ref: DataReference<'a>) -> Result<DataReference<'a>> {
        match data_ref {
            DataReference::Local(local) => self.dereference_data_ref(
                self.lookup_local(local)
                    .ok_or_else(|| {
                        eyre!(
                            "Attempted to deref a data reference pointing to a non existant local"
                        )
                    })?
                    .reference,
            ),
            DataReference::Const(constant) => {
                let (tokens, _sig) = self.lookup_definition(DefinitionIdent::Const(constant))
                    .ok_or_else(|| {
                        eyre!(
                            "Attempted to deref a data reference pointing to a non existant constant"
                        )
                    })?;

                if let [ClacToken::Number(num)] = &tokens[..] {
                    Ok(DataReference::Number(*num))
                } else {
                    Ok(DataReference::Const(constant))
                }
            }
            data_ref => Ok(data_ref),
        }
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
