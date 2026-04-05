pub mod builtins;
pub mod clac;
pub mod ir;
pub mod post_process;

use color_eyre::{
    Section,
    eyre::{Context, ContextCompat, OptionExt, Result, bail, eyre},
};
use pest::Span;
use tracing::{debug, trace};

use std::{
    borrow::Borrow,
    collections::{HashMap, HashSet},
    fmt::Debug,
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
    usize,
};

use crate::{
    ast::{
        DeferedCaptures, DeferedVersion, FunctionAttribute, FunctionSignature, IdentRef, Type,
        Value, VariableVersion,
    },
    codegen::{
        builtins::clac_builtins,
        clac::{ClacProgram, ClacToken, ClacValue, MangledIdent},
        ir::DataReference,
    },
    middleware::generate_span_error_section,
    type_check::TypeChecker,
};

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum DefinitionIdent<'a> {
    Function(IdentRef<'a>),
    Inline(IdentRef<'a>),
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TempoaryIdent(pub u64);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct BranchIdent(pub u64);

/// Represents an offset from bottom of the stack / start of the program
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Offset(pub ClacValue);

#[derive(Debug, Clone)]
pub struct AnnotatedDataRef<'a> {
    pub reference: DataReference<'a>,
    pub data_type: Type<'a>,
}

#[derive(Debug, Clone)]
pub enum MaybeTailCall<'a> {
    Regular(DataReference<'a>),
    TailCall {
        parameters: Vec<DataReference<'a>>,
        signature: FunctionSignature<'a>,
        tokens: Vec<ClacToken>,
        call_span: Span<'a>,
    },
}

impl<'a> MaybeTailCall<'a> {
    pub fn into_data_ref(self, ctx: &mut CodegenCtx<'a, '_>) -> Result<DataReference<'a>> {
        match self {
            MaybeTailCall::Regular(data_reference) => Ok(data_reference),
            MaybeTailCall::TailCall {
                parameters,
                signature,
                tokens,
                call_span,
            } => {
                let res: Result<_> = try {
                    let DeferedCaptures::ResolvedCaptures(captures) = &signature.captures else {
                        return Err(eyre!("COMPILER BUG: defered version was not resolved"));
                    };

                    ctx.bring_up_references(
                        captures
                            .0
                            .iter()
                            .map(|(_, _, version)| DataReference::Local(version.unwrap()))
                            .chain(parameters),
                        signature.paramater_width(ctx.type_checker)?,
                    )?;

                    for token in tokens.iter() {
                        ctx.push_token(token.clone())?;
                    }

                    DataReference::Tempoary(ctx.allocate_tempoary(signature.return_type.clone())?)
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
    locals: HashMap<VariableVersion, AnnotatedDataRef<'a>>,
    constants: HashMap<VariableVersion, Value<'a>>,
    temporaries: HashMap<TempoaryIdent, (Type<'a>, Offset)>,
    definitions: HashMap<StoredDefinitionIdent<'a>, (Vec<ClacToken>, FunctionSignature<'a>)>,

    allow_underflow: bool,
}

#[derive(Debug, Clone)]
pub struct CodegenCtx<'a, 'b> {
    pub type_checker: &'b TypeChecker<'a>,

    tokens: Vec<ClacToken>,
    scope_stack: Vec<ScopeFrame<'a>>,
    // Index of one past the top of the stack
    // Aka the length of the stack
    cursor: ClacValue,

    id_counter: Arc<AtomicU64>,
}

// FIXME: Many of these functions should be private
impl<'a, 'b> CodegenCtx<'a, 'b> {
    pub fn new(type_checker: &'b TypeChecker<'a>) -> Self {
        let mut ctx = Self {
            type_checker,
            tokens: Default::default(),
            scope_stack: Default::default(),
            cursor: Default::default(),
            id_counter: Arc::new(AtomicU64::new(0)),
        };

        for (ident, (code, sig)) in clac_builtins() {
            ctx.define_inline(&ident, sig, vec![code]);
        }

        // Allocates the first stack frame
        // Necessary to guarantee that the first stack frame starts at 0
        ctx.top_scope_frame();

        ctx
    }

    pub fn into_tokens(self) -> ClacProgram {
        ClacProgram(self.tokens)
    }

    fn make_scope_frame(&self, attributes: &HashSet<FunctionAttribute>) -> ScopeFrame<'a> {
        ScopeFrame {
            frame_start: self.cursor,
            locals: Default::default(),
            constants: Default::default(),
            temporaries: Default::default(),
            definitions: Default::default(),
            allow_underflow: attributes.contains(&FunctionAttribute::AllowUnderflow),
        }
    }

    fn push_scope_frame(&mut self, frame: ScopeFrame<'a>) -> &mut ScopeFrame<'a> {
        self.scope_stack.push_mut(frame)
    }

    fn pop_scope_frame(&mut self) -> Option<ScopeFrame<'a>> {
        self.scope_stack.pop()
    }

    fn top_scope_frame(&mut self) -> &mut ScopeFrame<'a> {
        if self.scope_stack.is_empty() {
            self.push_scope_frame(self.make_scope_frame(&Default::default()))
        } else {
            self.scope_stack.last_mut().unwrap()
        }
    }

    pub fn allocate_tempoary(&mut self, var_type: Type<'a>) -> Result<TempoaryIdent> {
        assert!(self.cursor >= var_type.width(self.type_checker)?);
        let offset = Offset(self.cursor - var_type.width(self.type_checker)?);

        Ok(self.allocate_tempoary_at(var_type, offset))
    }

    pub fn reference_relative(
        &mut self,
        var_type: Type<'a>,
        base: DataReference<'a>,
        rel_offset: Offset,
    ) -> Result<DataReference<'a>> {
        match self.dereference_data_ref(&base)? {
            DataReference::Value(value) => match var_type.resolve_once(self.type_checker)? {
                Type::Int => Ok(DataReference::Value(Value::Int(
                    value.as_repr()[rel_offset.0 as usize],
                ))),
                Type::Char => Ok(DataReference::Value(Value::Char(
                    value.as_repr()[rel_offset.0 as usize],
                ))),
                Type::Bool => Ok(DataReference::Value(Value::Bool(
                    value.as_repr()[rel_offset.0 as usize] != 0,
                ))),
                Type::Void => Ok(DataReference::Tempoary(self.allocate_tempoary(Type::Void)?)),
                _ => {
                    let start = rel_offset.0 as usize;
                    let end = start + var_type.width(self.type_checker)? as usize;

                    // TODO: is this actually a problem?
                    // warn!("Comptime Value::Flat emitted, value propagation may be impacted");

                    Ok(DataReference::Value(Value::Flat(
                        var_type.clone(),
                        value.as_repr()[start..end].to_vec(),
                    )))
                }
            },
            DataReference::Tempoary(tempoary_ident) => {
                let (base_type, base_offset) = self
                    .lookup_temporary(tempoary_ident)
                    .ok_or_eyre("Bad tempoary")?;
                assert!(0 <= rel_offset.0 && rel_offset.0 < base_type.width(self.type_checker)?);

                let offset = Offset(base_offset.0 + rel_offset.0);
                Ok(DataReference::Tempoary(
                    self.allocate_tempoary_at(var_type, offset),
                ))
            }
            _ => unreachable!(),
        }
    }

    fn allocate_tempoary_at(&mut self, var_type: Type<'a>, offset: Offset) -> TempoaryIdent {
        let ident = TempoaryIdent(self.id_counter.fetch_add(1, Ordering::Relaxed));

        self.top_scope_frame()
            .temporaries
            .insert(ident, (var_type, offset));

        ident
    }

    pub fn promote_to_local(
        &mut self,
        data_ref: DataReference<'a>,
        version: VariableVersion,
        var_type: Type<'a>,
    ) {
        self.top_scope_frame().locals.insert(
            version,
            AnnotatedDataRef {
                reference: data_ref,
                data_type: var_type,
            },
        );
    }

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

        let call = vec![ClacToken::Call {
            mangled_ident: mangled.clone(),
            stack_delta: signature.stack_delta(self.type_checker)?,
        }];
        self.top_scope_frame()
            .definitions
            .insert(StoredDefinitionIdent(def_ident), (call, signature.clone()));

        let original_cursor = self.cursor;
        self.push_token(ClacToken::StartDef {
            mangled_ident: mangled,
        })
        .unwrap();

        {
            let mut frame = self.make_scope_frame(&attributes);
            self.cursor += signature.paramater_width(self.type_checker)?;

            let id_counter = self.id_counter.clone();
            let mut offset = 0;

            for (var_type, _ident, version) in signature.arguements_and_captures()? {
                let DeferedVersion::ResolvedVersion(version) = version else {
                    return Err(eyre!(
                        "COMPILER BUG: attempted to define a function whose args have unresolved version"
                    ));
                };

                let cur_offset = Offset(frame.frame_start + offset);
                offset += var_type.width(self.type_checker)?;

                // Name arg as a temporary
                let tempoary = TempoaryIdent(id_counter.fetch_add(1, Ordering::Relaxed));
                frame
                    .temporaries
                    .insert(tempoary, (var_type.clone(), cur_offset));
                assert!(
                    frame
                        .locals
                        .insert(
                            *version,
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
            self.push_scope_frame(frame);

            let return_data_ref = (scope)(self)?;

            let (retain_width, tail_call) = match return_data_ref {
                MaybeTailCall::Regular(data_reference) => {
                    self.bring_up_references(
                        &[data_reference],
                        signature.return_width(self.type_checker)?,
                    )?;

                    (signature.return_width(self.type_checker)?, None)
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
                    if signature.return_type.width(self.type_checker)?
                        != tail_call_sig.return_type.width(self.type_checker)?
                    {
                        return Err(eyre!(
                            "Attempted to tail call `{ident}` but it returns a {:?}, and the calling runction returns a {:?}, and these types differ in width",
                            tail_call_sig.return_type,
                            signature.return_type
                        )).with_section(|| generate_span_error_section(call_span));
                    }

                    let DeferedCaptures::ResolvedCaptures(captures) = &tail_call_sig.captures
                    else {
                        return Err(eyre!("COMPILER BUG: defered version was not resolved"));
                    };

                    self.bring_up_references(
                        captures
                            .0
                            .iter()
                            .map(|(_, _, version)| DataReference::Local(version.unwrap()))
                            .chain(parameters),
                        tail_call_sig.paramater_width(self.type_checker)?,
                    )
                    .wrap_err("COMPILER BUG: error bringing up references for tail call")
                    .with_section(|| generate_span_error_section(call_span))?;

                    (
                        tail_call_sig.paramater_width(self.type_checker)?,
                        Some(tokens),
                    )
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
                    self.push_token(ClacToken::DropRange {
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

    pub fn define_const(&mut self, version: VariableVersion, value: Value<'a>) {
        self.top_scope_frame().constants.insert(version, value);
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
            .insert(StoredDefinitionIdent(def_ident), (tokens, sig));

        def_ident
    }

    /// Copies the data pointed to by the references to the top of the stack
    /// Stack after call: S, r_1, ..., r_n
    // TODO: Check types instead of widths

    pub fn bring_up_references(
        &mut self,
        references: impl IntoIterator<Item = impl Borrow<DataReference<'a>>>,
        expected_width: ClacValue,
    ) -> Result<()> {
        trace!("bring up references, expected_width, {expected_width}");

        // TODO: Optimize
        let starting_cursor = self.cursor;
        for reference in references {
            let reference = reference.borrow();
            trace!("bring up reference '{reference:?}'",);

            match reference {
                DataReference::Value(val) => {
                    for num in val.as_repr() {
                        self.push_token(ClacToken::Number(num))?
                    }
                }
                DataReference::Const(ident) => {
                    let val = self.lookup_const(ident).wrap_err("Bring up valid const")?;

                    for num in val.as_repr() {
                        self.push_token(ClacToken::Number(num))?
                    }
                }
                DataReference::Local(ident) => {
                    let AnnotatedDataRef {
                        reference,
                        data_type,
                    } = self.lookup_local(ident).wrap_err("Bring up valid local")?;

                    trace!("recursing to bring up local reference '{ident}'",);
                    self.bring_up_references(
                        &[reference.clone()],
                        data_type.width(self.type_checker)?,
                    )?;
                }
                &DataReference::Tempoary(ident) => {
                    let (var_type, offset) = self
                        .lookup_temporary(ident)
                        .expect("Bring up valid temporary");

                    if matches!(var_type.resolve_once(self.type_checker)?, Type::Void) {
                        continue;
                    }

                    let rel_offset = self.cursor - offset.0;
                    trace!(
                        "bring up reference '{reference:?}', cursor: {}, offset: {}, rel_offset: {}",
                        self.cursor, offset.0, rel_offset
                    );
                    for _ in 0..var_type.width(self.type_checker)? {
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
                "Type error?: expected to load width {expected_width}, actually loaded: {}",
                self.cursor - starting_cursor
            )
        }

        Ok(())
    }

    pub fn push_token(&mut self, token: ClacToken) -> Result<()> {
        self.cursor += token.stack_delta();

        if !self.top_scope_frame().allow_underflow {
            // Sanity check
            let frame_start = self.top_scope_frame().frame_start;
            assert!(
                self.cursor >= frame_start,
                "COMPILER BUG: underflowed stack frame on token `{token:?}`, cursor: {}, frame_start: {}",
                self.cursor,
                frame_start
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
            signature: sig.clone(),
            // TODO: Why is this making a new arc????
            tokens: func_impl.to_vec(),
            call_span,
        })
    }

    pub fn lookup_function_like_signature(
        &self,
        ident: IdentRef<'a>,
    ) -> Option<(&[ClacToken], &FunctionSignature<'a>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((func_impl, sig)) = frame.definitions.get(&DefinitionIdent::Inline(ident)) {
                return Some((func_impl, sig));
            }
            if let Some((func_impl, sig)) = frame.definitions.get(&DefinitionIdent::Function(ident))
            {
                return Some((func_impl, sig));
            }
        }

        None
    }

    pub fn lookup_definition(
        &self,
        ident: DefinitionIdent<'a>,
    ) -> Option<(&[ClacToken], &FunctionSignature<'a>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((func_impl, sig)) = frame.definitions.get(&ident) {
                return Some((func_impl, sig));
            }
        }

        None
    }

    pub fn lookup_const(&self, version: &VariableVersion) -> Option<Value<'a>> {
        for frame in self.scope_stack.iter().rev() {
            if let Some(value) = frame.constants.get(version) {
                return Some(value.clone());
            }
        }

        None
    }

    pub fn lookup_local(&self, version: &VariableVersion) -> Option<AnnotatedDataRef<'a>> {
        self.scope_stack
            .last()
            .and_then(|it| it.locals.get(version))
            .cloned()
    }

    pub fn lookup_ident(&self, version: &VariableVersion) -> Option<AnnotatedDataRef<'a>> {
        if let Some(local) = self.lookup_local(version) {
            Some(local)
        } else if let Some(constant) = self.lookup_const(version) {
            Some(AnnotatedDataRef {
                reference: DataReference::Value(constant.clone()),
                data_type: constant.compute_type(),
            })
        } else {
            None
        }
    }

    pub fn lookup_temporary(&self, ident: TempoaryIdent) -> Option<(Type<'a>, Offset)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((var_type, offset)) = frame.temporaries.get(&ident) {
                return Some((var_type.clone(), *offset));
            }
        }

        None
    }

    // pub fn lookup_ident_path(
    //     &mut self,
    //     mut var_path: &[IdentRef<'a>],
    // ) -> Result<AnnotatedDataRef<'a>> {
    //     let Some(var) = var_path.split_off_first() else {
    //         return Err(eyre!("Can not look up empty variable path"));
    //     };
    //
    //     let Some(mut lookup) = self.lookup_ident(var) else {
    //         return Err(eyre!("Variable {var}.{var_path:?} is not in scope"));
    //     };
    //
    //     while let [next, rem @ ..] = var_path {
    //         let (next_type, delta) = lookup
    //             .data_type
    //             .member_and_offset(self.type_checker, next)?;
    //
    //         match self.dereference_data_ref(&lookup.reference)? {
    //             DataReference::Tempoary(tempoary_ident) => {
    //                 let (_type, offset) = self
    //                     .lookup_temporary(tempoary_ident)
    //                     .ok_or_eyre("Bad tempoary")?;
    //
    //                 lookup.data_type = next_type.clone();
    //                 lookup.reference = DataReference::Tempoary(
    //                     self.allocate_tempoary_at(next_type, Offset(offset.0 + delta)),
    //                 );
    //             }
    //             DataReference::Value(Value::Struct(items)) => {
    //                 if let Some(value) = items.get(next) {
    //                     lookup.data_type = next_type.clone();
    //                     lookup.reference = DataReference::Value(value.clone());
    //                 } else {
    //                     return Err(eyre!(
    //                         "COMPILER BUG: Comptime struct value is missing field {next}"
    //                     ));
    //                 }
    //             }
    //             _ => {
    //                 return Err(eyre!(
    //                     "UNIMPLEMENTED: Can not access membors of a value that is not a temporary or a struct value"
    //                 ));
    //             }
    //         }
    //
    //         var_path = rem;
    //     }
    //
    //     Ok(lookup)
    // }

    pub fn dereference_data_ref(&self, data_ref: &DataReference<'a>) -> Result<DataReference<'a>> {
        match data_ref {
            DataReference::Local(local) => self.dereference_data_ref(
                &self
                    .lookup_local(local)
                    .ok_or_else(|| {
                        eyre!(
                            "Attempted to deref a data reference pointing to a non existant local"
                        )
                    })?
                    .reference,
            ),
            DataReference::Const(constant) => {
                let value = self.lookup_const(constant).ok_or_else(|| {
                    eyre!("Attempted to deref a data reference pointing to a non existant constant")
                })?;

                Ok(DataReference::Value(value))
            }
            data_ref => Ok(data_ref.clone()),
        }
    }
}

// Work around for a lifetime issue
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct StoredDefinitionIdent<'a>(pub DefinitionIdent<'a>);

impl<'a: 'b, 'b> std::borrow::Borrow<DefinitionIdent<'b>> for StoredDefinitionIdent<'a> {
    fn borrow(&self) -> &DefinitionIdent<'b> {
        &self.0
    }
}
