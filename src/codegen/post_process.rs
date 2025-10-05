use std::mem;

use crate::codegen::clac::{ClacProgram, ClacToken};

pub fn post_processers() -> Vec<Box<dyn PostProcesser>> {
    vec![
        Box::new(ExtractDefinitionsPostProcessor),
        Box::new(AttributionPostProcessor),
    ]
}

pub trait PostProcesser {
    fn process(&mut self, program: &mut ClacProgram);
}

#[derive(Default, Debug, Clone, Copy)]
pub struct ExtractDefinitionsPostProcessor;

impl PostProcesser for ExtractDefinitionsPostProcessor {
    fn process(&mut self, program: &mut ClacProgram) {
        let mut original = mem::take(program).0;

        let mut definitions = vec![];

        while let Some((end, _token)) = original
            .iter()
            .enumerate()
            .find(|(_, token)| matches!(token, ClacToken::EndDef))
        {
            let Some((start, _token)) = original
                .iter()
                .enumerate()
                .take(end)
                .rev()
                .find(|(_, token)| matches!(token, ClacToken::StartDef { .. }))
            else {
                panic!("ExtractDefinitions post processer encountered an unclosed definition");
            };

            definitions.push(original.drain(start..=end).collect::<Vec<_>>());
        }

        assert!(
            original
                .iter()
                .find(|token| matches!(token, ClacToken::StartDef { .. }))
                .is_none(),
            "ExtractDefinitions post processer encountered an unclosed definition"
        );

        let has_definitions = !definitions.is_empty();
        if has_definitions {
            program
                .0
                .push(ClacToken::Comment("Start Definitions".to_string()));
            for definition in definitions {
                program.0.extend_from_slice(&definition);
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
            "Compiled using Eoghan's flap to clac compiler".to_string(),
        ));
        program.0.push(ClacToken::NewLine);
        program.0.extend_from_slice(&original);
    }
}
