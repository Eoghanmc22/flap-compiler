use std::{
    collections::{BTreeMap, BTreeSet, HashSet},
    ffi::OsStr,
    fmt::Debug,
    fmt::Write as _,
    fs::{self, OpenOptions},
    io::Write as _,
    path::{Path, PathBuf},
};

use color_eyre::eyre::{Context, ContextCompat, Result, eyre};
use pest::Span;
use tracing::{debug, warn};

use crate::{
    ast::{AnnotatedSpan, Block, Directive},
    codegen::{
        CodegenCtx,
        clac::ClacProgram,
        post_process::{
            AttributionPostProcessor, CheckNativeWidth, ExtractDefinitionsPostProcessor,
            PostProcesser, SourceCodeCommentPostProcessor,
        },
    },
    middleware, parser,
    type_check::{TypeCheck, TypeChecker},
};

pub struct CompileContext {
    sources: BTreeMap<PathBuf, SourceFile>,
    root: PathBuf,
}

impl CompileContext {
    pub fn new(root: impl AsRef<Path>) -> Result<Self> {
        let root = fs::canonicalize(root.as_ref()).wrap_err("Get canonical path")?;

        let mut ctx = CompileContext {
            sources: Default::default(),
            root: root.clone(),
        };

        ctx.collect_sources(&root)?;

        Ok(ctx)
    }

    fn collect_sources(&mut self, file: impl AsRef<Path>) -> Result<()> {
        let file = fs::canonicalize(file.as_ref()).wrap_err("Get canonical path")?;

        if fs::metadata(&file)?.is_dir() {
            let mut source_file = SourceFile::default();

            for file in fs::read_dir(&file)? {
                let file = file?.path();
                let file = fs::canonicalize(file)?;

                if file.extension() != Some("flap".as_ref()) {
                    continue;
                }

                self.collect_sources(&file)?;
                source_file.includes.insert(file);
            }

            let file = fs::canonicalize(file)?;
            self.sources.insert(file, source_file);

            return Ok(());
        }

        if self.sources.contains_key(&file) {
            return Ok(());
        }

        let contents = fs::read_to_string(&file).wrap_err("Read file")?;

        let file_name = file.as_os_str().to_str().wrap_err("Path must be utf8")?;
        let directives = parser::parse_directives(&contents, &file_name)
            .map_err(|err| parser::map_parser_error(err, &file_name, &contents))
            .wrap_err("Parse program")?;

        let mut includes = BTreeSet::new();
        for directive in directives {
            match directive {
                Directive::Include(include_path, _) => {
                    let include_path = file.parent().unwrap().join(include_path);
                    let include_path = fs::canonicalize(&include_path).map_err(|err| {
                        eyre!(
                            "Could not canonicalize {include_path:?} referenced by {file:?}: {err}"
                        )
                    })?;

                    includes.insert(include_path);
                }
            }
        }

        self.sources.entry(file).or_insert(SourceFile {
            contents,
            includes: includes.clone(),
        });

        for include in &includes {
            self.collect_sources(include)?;
        }

        Ok(())
    }

    // TODO: Is this correct?
    pub fn flatten_imports<'a>(&'a self) -> Result<Block<'a>> {
        let mut seen = HashSet::new();
        let mut already_included = HashSet::new();
        let mut stack = Vec::new();
        let mut statements = Vec::new();

        stack.push(&self.root);

        while let Some(next) = stack.pop() {
            if already_included.contains(next) {
                continue;
            }
            seen.insert(next);

            let source = self.sources.get(next).unwrap();

            let ready = source
                .includes
                .iter()
                .all(|it| already_included.contains(it));

            if ready {
                let file_name = next.as_os_str().to_str().wrap_err("Path must be utf8")?;
                let program = parser::parse_program(&source.contents, &file_name)
                    .map_err(|err| parser::map_parser_error(err, &file_name, &source.contents))
                    .wrap_err("Parsing Error")?;

                statements.extend(program.code.statements.into_iter());
                already_included.insert(next);
            } else {
                stack.push(next);
                for include in &source.includes {
                    if !seen.contains(include) {
                        stack.push(include);
                    }
                }
                if let Some(top) = stack.last() {
                    if *top == next {
                        warn!("Cyclical imports detected at {next:?}");
                        stack.pop();
                    }
                }
            }
        }

        Ok(Block {
            statements,
            captures: Default::default(),
            span: AnnotatedSpan {
                span: Span::new("<merged sources>", 0, 16).unwrap(),
                file_name: "<merged sources>",
            },
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct SourceFile {
    contents: String,
    includes: BTreeSet<PathBuf>,
}

#[derive(Debug, Clone)]
pub struct CompileConfig {
    pub verbose_parsing_errors: bool,
    pub tree_shaking: bool,
    pub emit_native_width_assert: bool,
    pub emit_source_code_comment: bool,
    pub emit_attribution_comment: bool,
}

impl Default for CompileConfig {
    fn default() -> Self {
        Self {
            verbose_parsing_errors: false,
            tree_shaking: true,
            emit_native_width_assert: true,
            emit_source_code_comment: true,
            emit_attribution_comment: true,
        }
    }
}

pub fn compile(file: impl AsRef<Path> + Debug, config: CompileConfig) -> Result<ClacProgram> {
    let file = file.as_ref();

    if config.verbose_parsing_errors {
        pest::set_error_detail(true);
    }

    let ctx = CompileContext::new(file)?;
    let mut program = ctx.flatten_imports()?;
    debug!("Parsed AST: {program:#?}");

    let mut type_checker = TypeChecker::default();
    let return_type = program
        .check_and_resolve_types(&mut type_checker)
        .wrap_err("Type Check Program")?;

    let mut codegen = CodegenCtx::new(&type_checker);
    let tail_expr = middleware::walk_block(&mut codegen, &program).wrap_err("Ast to Clac")?;
    let tail_data_ref = tail_expr
        .into_data_ref(&mut codegen)
        .wrap_err("Get tail data ref")?;
    codegen
        .bring_up_references(&[tail_data_ref], return_type.width(&type_checker)?)
        .wrap_err("Bring up tail expr")?;

    let mut program = codegen.into_tokens();

    {
        // Code gen emits clac code with nested definitions which is not valid clac code
        // Flatten the definitions in this postprocessing step
        ExtractDefinitionsPostProcessor {
            tree_shaking: config.tree_shaking,
        }
        .process(&mut program);

        // Emit an assert that the runtime native width is the same as what the compiler expects
        if config.emit_native_width_assert {
            CheckNativeWidth.process(&mut program);
        }

        // Emit a comment containing the programs source code
        if config.emit_source_code_comment {
            let source_code = &ctx.sources.get(&ctx.root).unwrap().contents;

            SourceCodeCommentPostProcessor(source_code).process(&mut program);
        }

        // Emit a comment attributing the generated clac code to this compiler
        if config.emit_attribution_comment {
            AttributionPostProcessor.process(&mut program);
        }
    }

    Ok(program)
}

pub fn compile_to_string(file: impl AsRef<Path> + Debug, config: CompileConfig) -> Result<String> {
    let file = file.as_ref();

    let program = compile(file, config)?;

    let mut s = String::new();

    write!(&mut s, "{program}").wrap_err("Write code")?;

    Ok(s)
}

pub fn compile_to_file(file: impl AsRef<Path> + Debug, config: CompileConfig) -> Result<()> {
    let file = file.as_ref();

    let program = compile(file, config)?;

    let output_dir = PathBuf::from("out/");
    fs::create_dir_all(&output_dir).wrap_err("Create out dir")?;
    let out_file = output_dir.join(
        file.with_extension("clac")
            .file_name()
            .unwrap_or(OsStr::new("out.clac")),
    );

    let mut file = OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(out_file)
        .wrap_err("Open output file")?;
    write!(&mut file, "{program}").wrap_err("Write code")?;

    Ok(())
}
