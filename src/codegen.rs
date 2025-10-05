pub mod builtins;
pub mod clac;
pub mod ir;
pub mod post_process;

use color_eyre::eyre::{ContextCompat, Result, bail};

use std::{
    collections::{HashMap, HashSet},
    sync::{
        Arc,
        atomic::{AtomicU64, Ordering},
    },
};

use crate::{
    ast::{FunctionAttribute, Ident, IdentRef, Type, Value},
    codegen::{
        builtins::clac_builtins,
        clac::{ClacProgram, ClacToken, MangledIdent},
        ir::{ClacOp, DataReference, FunctionSignature},
    },
};

static TEMPOARY_COUNTER: AtomicU64 = AtomicU64::new(0);
static FUNCTION_COUNTER: AtomicU64 = AtomicU64::new(0);
static CONST_COUNTER: AtomicU64 = AtomicU64::new(0);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum DefinitionIdent<'a> {
    Function(IdentRef<'a>),
    Builtin(IdentRef<'a>),
    Const(IdentRef<'a>),
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct TempoaryIdent(pub u64);

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct BranchIdent(pub u64);

/// Repersents an offset from bottom of the stack / start of the program
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Offset(pub i32);

#[derive(Debug, Clone)]
pub struct ScopeFrame<'a> {
    frame_start: i32,
    locals: HashMap<IdentRef<'a>, (Type, DataReference<'a>)>,
    temporaries: HashMap<TempoaryIdent, (Type, Offset)>,
    definitions: HashMap<StoredDefinitionIdent<'a>, (MangledIdent, Arc<FunctionSignature<'a>>)>,
}

#[derive(Debug, Clone)]
pub struct CodegenCtx<'a> {
    tokens: Vec<ClacToken>,
    scope_stack: Vec<ScopeFrame<'a>>,
    // Index of one past the top of the stack
    // Aka the length of the stack
    cursor: i32,

    // TODO: I dont like builtins being this special
    builtins: HashMap<Ident, (Vec<ClacToken>, Arc<FunctionSignature<'a>>)>,
}

impl Default for CodegenCtx<'_> {
    fn default() -> Self {
        let mut ctx = Self {
            tokens: Default::default(),
            scope_stack: Default::default(),
            cursor: Default::default(),
            builtins: Default::default(),
        };

        for (ident, (code, sig)) in clac_builtins() {
            ctx.define_builtin(&ident, sig, code);
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

    fn push_scope_frame(&mut self) -> &mut ScopeFrame<'a> {
        self.scope_stack.push_mut(ScopeFrame {
            frame_start: self.cursor,
            locals: Default::default(),
            temporaries: Default::default(),
            definitions: Default::default(),
        })
    }

    fn pop_scope_frame(&mut self) -> Option<ScopeFrame<'a>> {
        self.scope_stack.pop()
    }

    fn top_scope_frame(&mut self) -> &mut ScopeFrame<'a> {
        if self.scope_stack.is_empty() {
            self.push_scope_frame()
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

    pub fn define_function<F: FnOnce(&mut Self) -> Result<DataReference<'a>>>(
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
                mangled.clone(),
                // TODO: Remove clone
                signature.clone(),
            ),
        );

        let original_cursor = self.cursor;
        self.push_token(ClacToken::StartDef {
            mangled_ident: mangled,
        })
        .unwrap();

        {
            self.push_scope_frame();
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

            self.bring_up_references(&[return_data_ref], signature.return_width())?;

            let frame = self.pop_scope_frame().unwrap();
            let needs_dropping = self.cursor - frame.frame_start - signature.return_width() as i32;

            assert!(needs_dropping >= 0);

            for _ in 0..needs_dropping {
                // TODO: Optimize, generalize
                if signature.return_width() > 0 {
                    assert_eq!(signature.return_width(), 1);
                    self.push_token(ClacToken::Swap)?;
                }
                self.push_token(ClacToken::Drop)?;
            }

            assert_eq!(
                self.cursor - frame.frame_start,
                signature.return_width() as i32
            );
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
        let num = CONST_COUNTER.fetch_add(1, Ordering::Relaxed);

        let mangled = format!("const-{}-{}", ident, num);
        let mangled = MangledIdent(Arc::new(mangled));

        let signature = Arc::new(FunctionSignature {
            arguements: vec![],
            return_type: var_type,
        });

        self.top_scope_frame().definitions.insert(
            StoredDefinitionIdent(def_ident),
            (mangled.clone(), signature),
        );

        self.push_token(ClacToken::StartDef {
            mangled_ident: mangled,
        })
        .unwrap();

        {
            self.push_scope_frame();
            self.push_token(ClacToken::Number(value.as_repr()))?;
            self.pop_scope_frame();
        }

        self.push_token(ClacToken::EndDef)?;

        Ok(def_ident)
    }

    pub fn define_builtin(
        &mut self,
        ident: IdentRef<'a>,
        sig: FunctionSignature<'a>,
        code: Vec<ClacToken>,
    ) {
        self.builtins
            .insert(ident.to_string(), (code, Arc::new(sig)));
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
                    let (mangled, sig) = self
                        .lookup_definition(DefinitionIdent::Const(ident))
                        .wrap_err("Bring up valid const")?;

                    self.push_token(ClacToken::Call {
                        mangled_ident: mangled.clone(),
                        stack_delta: sig.stack_delta(),
                    })?;
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

        // Sanity check
        assert!(
            self.cursor >= self.top_scope_frame().frame_start,
            "COMPILER BUG: underflowed stack frame on token `{token:?}`"
        );

        self.tokens.push(token);

        Ok(())
    }

    pub fn call_function_like(
        &mut self,
        ident: IdentRef<'a>,
        parameters: Vec<DataReference<'a>>,
    ) -> Result<DataReference<'a>> {
        // TODO: Try to get rid of clone
        let tempoary = if let Some((inline_code, sig)) = self.builtins.get_mut(ident).cloned() {
            self.bring_up_references(&parameters, sig.paramater_width())?;

            for clac_token in inline_code {
                self.push_token(clac_token)?;
            }
            self.allocate_tempoary(sig.return_type)
        } else {
            let clac_op = ClacOp::Call {
                name: crate::codegen::DefinitionIdent::Function(ident),
                parameters,
            };

            clac_op.append_into(self)?.unwrap()
        };

        Ok(DataReference::Tempoary(tempoary))
    }

    pub fn lookup_function_like_signature(
        &self,
        ident: IdentRef<'a>,
    ) -> Option<Arc<FunctionSignature<'a>>> {
        if let Some((_inline_code, sig)) = self.builtins.get(ident) {
            Some(sig.clone())
        } else {
            self.lookup_definition(DefinitionIdent::Function(ident))
                .map(|(_mangled, sig)| sig)
        }
    }

    pub fn lookup_definition(
        &self,
        ident: DefinitionIdent,
    ) -> Option<(MangledIdent, Arc<FunctionSignature<'a>>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((mangled, sig)) = frame.definitions.get(&ident) {
                return Some((mangled.clone(), sig.clone()));
            }
        }

        None
    }

    pub fn lookup_local(&self, ident: IdentRef) -> Option<(Type, DataReference<'a>)> {
        for frame in self.scope_stack.iter().rev() {
            if let Some((var_type, data_ref)) = frame.locals.get(ident) {
                return Some((*var_type, *data_ref));
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
        for frame in self.scope_stack.iter().rev() {
            if let Some((var_type, _)) = frame.locals.get(ident) {
                return Some((DataReference::Local(ident), *var_type));
            }
            if let Some((_, sig)) = frame.definitions.get(&DefinitionIdent::Const(ident)) {
                return Some((DataReference::Const(ident), sig.return_type));
            }
            // TODO: Is there anything else to check?
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
