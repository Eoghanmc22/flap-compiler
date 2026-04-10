use color_eyre::eyre::WrapErr;
use std::{
    backtrace::Backtrace,
    collections::{BTreeMap, HashMap, HashSet},
    ffi::OsStr,
    fmt::{self, Debug, Write as _},
    fs::{self, OpenOptions},
    io::{self, Write as _},
    path::{Path, PathBuf},
    rc::Rc,
};

use pest::Span;
use tracing::{debug, warn};

use crate::{
    ast::{AnnotatedSpan, Block, Directive, OwnedSpan, Program},
    codegen::{
        CodegenCtx,
        clac::ClacProgram,
        post_process::{
            AttributionPostProcessor, CheckNativeWidth, ExtractDefinitionsPostProcessor,
            PostProcesser, SourceCodeCommentPostProcessor,
        },
    },
    error::CompileError,
    middleware, parser,
    type_check::{TypeCheck, TypeChecker},
};

type Result<'a, T, E = CompileError<'a>> = core::result::Result<T, E>;

pub struct CompileContext {
    sources: BTreeMap<PathBuf, SourceFile>,
    root: PathBuf,
    config: CompileConfig,
}

pub type FileCache<'a> = HashMap<&'a Path, &'a str>;

impl CompileContext {
    pub fn new(
        root: impl AsRef<Path>,
        file_cache: &FileCache,
        config: CompileConfig,
    ) -> Result<'static, Self> {
        let root = fs::canonicalize(root.as_ref())?;

        let mut ctx = CompileContext {
            sources: Default::default(),
            root: root.clone(),
            config,
        };

        ctx.collect_sources(&root, file_cache)?;

        Ok(ctx)
    }

    fn collect_sources(
        &mut self,
        file: impl AsRef<Path>,
        file_cache: &FileCache,
    ) -> Result<'static, ()> {
        let file = fs::canonicalize(file.as_ref())?;

        if fs::metadata(&file)?.is_dir() {
            let mut source_file = SourceFile::default();

            for file in fs::read_dir(&file)? {
                let file = file?.path();
                let file = fs::canonicalize(file)?;

                if file.extension() != Some("flap".as_ref()) {
                    continue;
                }

                self.collect_sources(&file, file_cache)?;

                let span = OwnedSpan::new("<dir contents>", file.to_string_lossy());
                source_file.includes.insert(file, span);
            }

            let file = fs::canonicalize(file)?;
            self.sources.insert(file, source_file);

            return Ok(());
        }

        if self.sources.contains_key(&file) {
            return Ok(());
        }

        let contents = file_cache
            .get(file.as_path())
            .map(|it| Ok(it.to_string()))
            .unwrap_or_else(|| fs::read_to_string(&file))?;

        let file_name = file.as_os_str().to_str().ok_or(CompileError::NonUtf8Path)?;
        let directives = parser::parse_directives(&contents, &file_name)
            .map_err(|err| parser::map_parser_error(err, &file_name, &contents))?;

        let mut includes = BTreeMap::new();
        for directive in directives {
            match directive {
                Directive::Include(include_path, span) => {
                    let include_path = file.parent().unwrap().join(include_path);
                    let include_path = fs::canonicalize(&include_path)?;

                    includes.insert(include_path, span.into());
                }
            }
        }

        self.sources.entry(file).or_insert(SourceFile {
            contents,
            includes: includes.clone(),
        });

        for (include, _) in &includes {
            self.collect_sources(include, file_cache)?;
        }

        Ok(())
    }

    // TODO: Is this correct?
    pub fn collect_segments<'a>(&'a self) -> Vec<Segment<'a>> {
        let mut seen = HashSet::new();
        let mut already_included = HashSet::new();
        let mut stack = Vec::new();
        let mut segments = Vec::new();

        stack.push((&self.root, Rc::new(SegmentPath::TopLevel)));

        while let Some((next, segment)) = stack.pop() {
            if already_included.contains(next) {
                continue;
            }
            seen.insert(next);

            let source = self.sources.get(next).unwrap();

            let ready = source
                .includes
                .keys()
                .all(|it| already_included.contains(it));

            if ready {
                let res = try {
                    let file_name = next.as_os_str().to_str().ok_or(CompileError::NonUtf8Path)?;
                    parser::parse_program(&source.contents, &file_name).map_err(|err| {
                        parser::map_parser_error(err, &file_name, &source.contents).into()
                    })?
                };

                segments.push(Segment {
                    ast: res,
                    path: segment.to_vec(),
                });
                already_included.insert(next);
            } else {
                stack.push((next, segment.clone()));
                for (include, span) in &source.includes {
                    if !seen.contains(include) {
                        let sub_segment = SegmentPath::Imported(&span, segment.clone());
                        stack.push((include, Rc::new(sub_segment)));
                    }
                }
                if let Some((top, _)) = stack.last() {
                    if *top == next {
                        warn!("Cyclical imports detected at {next:?}");
                        stack.pop();
                    }
                }
            }
        }

        segments
    }

    pub fn flatten_imports<'a>(&'a self) -> Result<Block<'a>> {
        let segments = self.collect_segments();

        let res = segments
            .into_iter()
            .map(|it| it.ast)
            .collect::<Result<Vec<_>>>()?;
        let statements = res.into_iter().flat_map(|it| it.code.statements).collect();

        Ok(Block {
            statements,
            captures: Default::default(),
            span: AnnotatedSpan {
                span: Span::new("<merged sources>", 0, 16).unwrap(),
                file_name: "<merged sources>",
            },
        })
    }

    pub fn root(&self) -> &SourceFile {
        self.sources.get(&self.root).unwrap()
    }

    pub fn config(&self) -> &CompileConfig {
        &self.config
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Default)]
pub struct SourceFile {
    pub contents: String,
    pub includes: BTreeMap<PathBuf, OwnedSpan>,
}

#[derive(Debug, PartialEq, Eq, Clone)]
enum SegmentPath<'a> {
    TopLevel,
    Imported(&'a OwnedSpan, Rc<SegmentPath<'a>>),
}

impl<'a> SegmentPath<'a> {
    pub fn to_vec(&self) -> Vec<&'a OwnedSpan> {
        let mut vec = vec![];

        let mut cur = self;
        while let SegmentPath::Imported(span, next) = cur {
            vec.push(*span);
            cur = next;
        }

        vec
    }
}

pub struct Segment<'a> {
    pub path: Vec<&'a OwnedSpan>,
    pub ast: Result<'a, Program<'a>>,
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

pub fn compile(ctx: &CompileContext) -> Result<ClacProgram> {
    let config = ctx.config();

    if config.verbose_parsing_errors {
        pest::set_error_detail(true);
    }

    let mut program = ctx.flatten_imports()?;
    debug!("Parsed AST: {program:#?}");

    let mut type_checker = TypeChecker::default();
    let return_type = program
        .check_and_resolve_types(&mut type_checker)
        .map_err(CompileError::TypeCheck)?;

    let mut codegen = CodegenCtx::new(&type_checker);
    let tail_expr = middleware::walk_block(&mut codegen, &program)?;
    let tail_data_ref = tail_expr.into_data_ref(&mut codegen)?;
    codegen.bring_up_references(&[tail_data_ref], return_type.width(&type_checker)?)?;

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

pub fn compile_to_string(ctx: &CompileContext) -> Result<String> {
    let program = compile(ctx)?;

    let mut s = String::new();

    write!(&mut s, "{program}")?;

    Ok(s)
}

pub fn compile_to_file(ctx: &CompileContext) -> Result<()> {
    let program = compile(ctx)?;

    let output_dir = PathBuf::from("out/");
    fs::create_dir_all(&output_dir)?;
    let out_file = output_dir.join(
        ctx.root
            .with_extension("clac")
            .file_name()
            .unwrap_or(OsStr::new("out.clac")),
    );

    let mut file = OpenOptions::new()
        .create(true)
        .truncate(true)
        .write(true)
        .open(out_file)?;
    write!(&mut file, "{program}")?;

    Ok(())
}
