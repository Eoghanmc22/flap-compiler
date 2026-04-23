use std::{
    backtrace::Backtrace,
    collections::{BTreeMap, HashMap, HashSet},
    mem,
};

use crate::{
    ast::{AnnotatedSpan, FunctionAttribute, Value},
    codegen::{
        CodegenCtx,
        clac::{ClacProgram, ClacToken, ClacValue, MangledIdent},
        ir::DataReference,
    },
    error::{CodegenError, CompileError},
    type_check::{self, TypeChecker},
};

type Result<'a, T, E = CompileError<'a>> = core::result::Result<T, E>;

pub trait PostProcesser<'a> {
    fn process(&mut self, program: &mut ClacProgram) -> Result<'a, ()>;
}

pub struct AllocateGlobals<'a, 'b> {
    pub type_checker: &'b TypeChecker<'a>,
}

impl<'a, 'b> PostProcesser<'a> for AllocateGlobals<'a, 'b> {
    fn process(&mut self, program: &mut ClacProgram) -> Result<'a, ()> {
        let last_global = self.type_checker.allocate_address(0);
        if last_global == type_check::GLOBAL_ARENA_START {
            return Ok(());
        }

        // TODO: improve
        let Some((sig, _)) = self.type_checker.lang_items.get("map_global") else {
            return Err(
                CodegenError::UnknownFunction("map_global", Backtrace::force_capture()).into(),
            );
        };

        let mut codegen = CodegenCtx::new(self.type_checker);

        codegen.define_function_stub(
            "map_global",
            sig.clone(),
            &HashSet::from([FunctionAttribute::NoMangle]),
        )?;

        codegen
            .call_function_like(
                "map_global",
                vec![
                    DataReference::Value(Value::Int(type_check::GLOBAL_ARENA_START), None),
                    DataReference::Value(
                        Value::Int(last_global - type_check::GLOBAL_ARENA_START),
                        None,
                    ),
                ],
                AnnotatedSpan::builtin(),
            )?
            .into_data_ref(&mut codegen)?;

        let origional = mem::replace(program, codegen.into_tokens());
        program.0.extend(origional.0);

        Ok(())
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct ExtractDefinitionsPostProcessor {
    pub tree_shaking: bool,
}

impl PostProcesser<'static> for ExtractDefinitionsPostProcessor {
    fn process(&mut self, program: &mut ClacProgram) -> Result<'static, ()> {
        let mut original = mem::take(program).0;

        let mut definitions = HashMap::new();

        while let Some((end, _token)) = original
            .iter()
            .enumerate()
            .find(|(_, token)| matches!(token, ClacToken::EndDef))
        {
            let Some((start, ClacToken::StartDef { mangled_ident })) = original
                .iter()
                .enumerate()
                .take(end)
                .rev()
                .find(|(_, token)| matches!(token, ClacToken::StartDef { .. }))
            else {
                panic!("ExtractDefinitions post processer encountered an unclosed definition");
            };

            let old = definitions.insert(
                mangled_ident.clone(),
                original.drain(start..=end).collect::<Vec<_>>(),
            );
            assert!(old.is_none());
        }

        assert!(
            original
                .iter()
                .find(|token| matches!(token, ClacToken::StartDef { .. }))
                .is_none(),
            "ExtractDefinitions post processer encountered an unclosed definition"
        );

        let mut referenced_definitions = BTreeMap::new();

        fn build_referenced_definitions<'b, 'a: 'b>(
            referenced_definitions: &'b mut BTreeMap<&'a MangledIdent, &'a [ClacToken]>,
            definitions: &mut HashMap<&'a MangledIdent, &'a [ClacToken]>,
            code: &'a [ClacToken],
        ) {
            for token in code {
                match token.canonicalize() {
                    ClacToken::Call { mangled_ident, .. } => {
                        if let Some(defn) = definitions.remove(mangled_ident) {
                            let old = referenced_definitions.insert(mangled_ident, &defn);
                            assert!(old.is_none());

                            build_referenced_definitions(
                                referenced_definitions,
                                definitions,
                                &defn,
                            );
                        } else {
                            assert!(
                                referenced_definitions.contains_key(mangled_ident),
                                "{mangled_ident:?}"
                            );
                        }
                    }
                    _ => {}
                }
            }
        }

        if self.tree_shaking {
            build_referenced_definitions(
                &mut referenced_definitions,
                &mut definitions
                    .iter()
                    .map(|(key, val)| (key, val.as_slice()))
                    .collect(),
                &original,
            );
        } else {
            referenced_definitions = definitions
                .iter()
                .map(|(key, val)| (key, val.as_slice()))
                .collect();
        }

        let has_definitions = !referenced_definitions.is_empty();
        if has_definitions {
            program
                .0
                .push(ClacToken::Comment("Start Definitions".to_string()));
            for definition in referenced_definitions.values() {
                program.0.extend_from_slice(definition);
                program.0.push(ClacToken::NewLine);
            }
        }

        if !original.is_empty() {
            if has_definitions {
                program.0.push(ClacToken::NewLine);
            }
            program.0.push(ClacToken::Comment("Start Main".to_string()));
            program.0.extend_from_slice(&original);
        }

        Ok(())
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct AttributionPostProcessor;

impl PostProcesser<'static> for AttributionPostProcessor {
    fn process(&mut self, program: &mut ClacProgram) -> Result<'static, ()> {
        let original = mem::take(program).0;

        program.0.push(ClacToken::Comment(
            "Compiled using Eoghan's flap to clac compiler https://github.com/Eoghanmc22/flap-compiler".to_string(),
        ));
        program.0.push(ClacToken::NewLine);
        program.0.extend_from_slice(&original);

        Ok(())
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct SourceCodeCommentPostProcessor<'a>(pub &'a str);

impl PostProcesser<'static> for SourceCodeCommentPostProcessor<'_> {
    fn process(&mut self, program: &mut ClacProgram) -> Result<'static, ()> {
        let original = mem::take(program).0;

        let mut comment = String::new();

        comment.push_str("flap source code:\n");
        for line in (self.0.trim()).lines() {
            comment.push_str("    ");
            comment.push_str(line);
            comment.push('\n');
        }
        program.0.push(ClacToken::Comment(comment));

        // program.0.push(ClacToken::NewLine);
        // program
        //     .0
        //     .push(ClacToken::Comment("flap source code".to_string()));

        // for line in self.0.lines() {
        //     program.0.push(ClacToken::Comment(line.to_string()));
        // }
        // program.0.push(ClacToken::Comment(self.0.to_string()));

        program.0.push(ClacToken::NewLine);
        program.0.extend_from_slice(&original);

        Ok(())
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct CheckNativeWidth;

impl PostProcesser<'static> for CheckNativeWidth {
    fn process(&mut self, program: &mut ClacProgram) -> Result<'static, ()> {
        let original = mem::take(program).0;

        program.0.push(ClacToken::Comment(
            "Check that the clac interperter is using the correct native width".into(),
        ));

        program
            .0
            .push(ClacToken::Number(ClacValue::BITS as ClacValue));
        program.0.push(ClacToken::Call {
            mangled_ident: MangledIdent("width_native".to_string().into()),
            stack_delta: 1,
        });
        program.0.push(ClacToken::Sub);
        program.0.push(ClacToken::If);
        program.0.push(ClacToken::Number(-100));
        program.0.push(ClacToken::Print);
        program.0.push(ClacToken::Quit);
        program.0.push(ClacToken::NewLine);
        program.0.push(ClacToken::NewLine);

        program.0.extend_from_slice(&original);

        Ok(())
    }
}
