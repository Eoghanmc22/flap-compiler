use std::{
    collections::{BTreeMap, HashMap},
    mem,
};

use crate::codegen::clac::{ClacProgram, ClacToken, ClacValue, MangledIdent};

pub trait PostProcesser {
    fn process(&mut self, program: &mut ClacProgram);
}

#[derive(Default, Debug, Clone, Copy)]
pub struct ExtractDefinitionsPostProcessor {
    pub tree_shaking: bool,
}

impl PostProcesser for ExtractDefinitionsPostProcessor {
    fn process(&mut self, program: &mut ClacProgram) {
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
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct AttributionPostProcessor;

impl PostProcesser for AttributionPostProcessor {
    fn process(&mut self, program: &mut ClacProgram) {
        let original = mem::take(program).0;

        program.0.push(ClacToken::Comment(
            "Compiled using Eoghan's flap to clac compiler https://github.com/Eoghanmc22/flap-compiler".to_string(),
        ));
        program.0.push(ClacToken::NewLine);
        program.0.extend_from_slice(&original);
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct SourceCodeCommentPostProcessor<'a>(pub &'a str);

impl PostProcesser for SourceCodeCommentPostProcessor<'_> {
    fn process(&mut self, program: &mut ClacProgram) {
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
    }
}

#[derive(Default, Debug, Clone, Copy)]
pub struct CheckNativeWidth;

impl PostProcesser for CheckNativeWidth {
    fn process(&mut self, program: &mut ClacProgram) {
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
    }
}
