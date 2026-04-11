use std::borrow::Cow;
use std::cell::RefCell;
use std::collections::HashMap;
use std::error::Error;
use std::fmt::Write as _;
use std::rc::Rc;
use std::sync::LazyLock;

use lsp_server::{Connection, Message, Request as ServerRequest, RequestId, Response};
use lsp_types::notification::{DidCloseTextDocument, Notification as _}; // for METHOD consts
use lsp_types::request::{Request, WorkspaceDiagnosticRefresh};
use lsp_types::{
    CompletionItem,
    CompletionItemKind,
    // capability helpers
    CompletionOptions,
    CompletionResponse,
    Diagnostic,
    DiagnosticSeverity,
    DidChangeTextDocumentParams,
    DidOpenTextDocumentParams,
    Hover,
    HoverContents,
    HoverProviderCapability,
    // core
    InitializeParams,
    MarkedString,
    OneOf,
    Position,
    PublishDiagnosticsParams,
    Range,
    ServerCapabilities,
    TextDocumentSyncCapability,
    TextDocumentSyncKind,
    Uri,
    // notifications
    notification::{DidChangeTextDocument, DidOpenTextDocument, PublishDiagnostics},
    // requests
    request::{Completion, GotoDefinition, HoverRequest},
};
use lsp_types::{
    CompletionItemLabelDetails, CompletionParams, DiagnosticRelatedInformation,
    DidCloseTextDocumentParams, Documentation, HoverParams, Location, MarkupContent, MarkupKind,
    NumberOrString,
};
use pest::Span;
use regex::Regex;
use tracing::{error, info};

use crate::ast::{self, AnnotatedSpan, Block, Program};
use crate::compile::{self, CompileConfig, CompileContext, FileCache};
use crate::error::IntoSpans;
use crate::lsp::ast_cache::{CachedParsedAst, CachedTypedAst};
use crate::parser;
use crate::type_check::{TypeCheck, TypeChecker, VariableKind};

mod ast_cache {
    use std::{mem, rc::Rc};

    use lsp_types::Diagnostic;

    use crate::{
        ast::{Block, Program},
        compile::CompileContext,
        type_check::TypeChecker,
    };

    #[derive(Clone)]
    pub struct CachedParsedAst {
        // NOTE: These lifetimes aren't really static,
        // they represent the lifetime of whats behind the Rc.
        parsed: Program<'static>,

        // These needs to be last since it needs to be dropped after the other fields
        _file_name: Rc<str>,
        _contents: Rc<str>,
    }

    impl CachedParsedAst {
        pub fn new<F, E>(file_name: Rc<str>, contents: Rc<str>, parse: F) -> Result<Self, E>
        where
            F: for<'a> Fn(&'a str, &'a str) -> Result<Program<'a>, E>,
        {
            let file_name_ref = &file_name;
            let content_ref = &contents;
            let parsed = (parse)(file_name_ref, content_ref)?;
            let parsed = unsafe { mem::transmute(parsed) };

            Ok(Self {
                parsed,
                _contents: contents,
                _file_name: file_name,
            })
        }

        pub fn parsed<'a>(&'a self) -> &'a Program<'a> {
            &self.parsed
        }
    }

    #[derive(Clone)]
    pub struct CachedTypedAst {
        // NOTE: These lifetimes aren't really static,
        // they represent the lifetime of whats behind the Rc.
        type_checker: TypeChecker<'static>,
        block: Block<'static>,

        // This needs to be last since it needs to be dropped after the other fields
        _contents: Rc<CompileContext>,
    }

    impl CachedTypedAst {
        pub fn new<F>(ctx: Rc<CompileContext>, type_check: F) -> (Self, Vec<Diagnostic>)
        where
            F: for<'a> Fn(&'a CompileContext) -> (TypeChecker<'a>, Block<'a>, Vec<Diagnostic>),
        {
            let ctx_ref = &ctx;
            let (type_checker, block, diagnostics) = (type_check)(ctx_ref);

            let type_checker = unsafe { mem::transmute(type_checker) };
            let block = unsafe { mem::transmute(block) };

            (
                Self {
                    type_checker,
                    block,
                    _contents: ctx,
                },
                diagnostics,
            )
        }

        pub fn type_checker<'a>(&'a self) -> &'a TypeChecker<'a> {
            &self.type_checker
        }

        pub fn block<'a>(&'a self) -> &'a Block<'a> {
            &self.block
        }
    }
}

type Result<T, E = Box<dyn Error + Send + Sync + 'static>> = std::result::Result<T, E>;
type DocumentMap = HashMap<Uri, Rc<Document>>;

struct Document {
    uri: Uri,
    file_name: Rc<str>,
    contents: Rc<str>,
    version: i32,

    parsed_ast: RefCell<Option<ast_cache::CachedParsedAst>>,
    typed_ast: RefCell<Option<ast_cache::CachedTypedAst>>,
}

pub fn start_lsp() -> Result<()> {
    info!("starting flap-ls");

    // transport
    let (connection, io_thread) = Connection::stdio();

    // advertised capabilities
    // TODO: https://www.robertsiliciano.com/notes/lsp-syntax-highlighting/
    let caps = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        completion_provider: Some(CompletionOptions::default()),
        definition_provider: Some(OneOf::Left(true)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        document_formatting_provider: Some(OneOf::Left(false)),
        // semantic_tokens_provider: todo!(),
        ..Default::default()
    };
    let init_params = connection.initialize(serde_json::json!(caps))?;
    main_loop(connection, init_params)?;
    io_thread.join()?;

    info!("shutting down server");

    Ok(())
}

// =====================================================================
// event loop
// =====================================================================

fn main_loop(connection: Connection, params: serde_json::Value) -> Result<()> {
    let _init: InitializeParams = serde_json::from_value(params)?;
    let mut docs: DocumentMap = HashMap::default();

    for msg in &connection.receiver {
        // eprintln!("{msg:?}");

        match msg {
            Message::Request(req) => {
                if connection.handle_shutdown(&req)? {
                    break;
                }
                if let Err(err) = handle_request(&connection, &req, &mut docs) {
                    error!("[lsp] request {} failed: {err}", &req.method);
                }
            }
            Message::Notification(note) => {
                if let Err(err) = handle_notification(&connection, &note, &mut docs) {
                    error!("[lsp] notification {} failed: {err}", note.method);
                }
            }
            Message::Response(resp) => info!("[lsp] response: {resp:?}"),
        }
    }
    Ok(())
}

// =====================================================================
// notifications
// =====================================================================

fn handle_notification(
    conn: &Connection,
    note: &lsp_server::Notification,
    docs: &mut DocumentMap,
) -> Result<()> {
    match note.method.as_str() {
        DidOpenTextDocument::METHOD => {
            let p: DidOpenTextDocumentParams = serde_json::from_value(note.params.clone())?;
            let doc = Rc::new(Document {
                contents: p.text_document.text.into(),
                version: p.text_document.version,
                file_name: p.text_document.uri.path().as_str().into(),
                uri: p.text_document.uri,
                parsed_ast: None.into(),
                typed_ast: None.into(),
            });

            docs.insert(doc.uri.clone(), doc.clone());

            let file_cache = make_file_cache(docs);
            build_asts_and_send_diagnostics(conn, &doc, &file_cache)?;
        }
        DidChangeTextDocument::METHOD => {
            let p: DidChangeTextDocumentParams = serde_json::from_value(note.params.clone())?;
            if let Some(change) = p.content_changes.into_iter().next() {
                let (parsed_ast, typed_ast) = docs
                    .remove(&p.text_document.uri)
                    .map(|it| {
                        (
                            it.parsed_ast.borrow().clone(),
                            it.typed_ast.borrow().clone(),
                        )
                    })
                    .unwrap_or((None, None));

                let doc = Rc::new(Document {
                    contents: change.text.into(),
                    version: p.text_document.version,
                    file_name: p.text_document.uri.path().as_str().into(),
                    uri: p.text_document.uri,
                    parsed_ast: parsed_ast.into(),
                    typed_ast: typed_ast.into(),
                });

                docs.insert(doc.uri.clone(), doc.clone());

                let file_cache = make_file_cache(docs);
                build_asts_and_send_diagnostics(conn, &doc, &file_cache)?;
            }
        }
        DidCloseTextDocument::METHOD => {
            let p: DidCloseTextDocumentParams = serde_json::from_value(note.params.clone())?;
            docs.remove(&p.text_document.uri);
        }
        _ => {}
    }
    Ok(())
}

// =====================================================================
// requests
// =====================================================================

fn handle_request(conn: &Connection, req: &ServerRequest, docs: &mut DocumentMap) -> Result<()> {
    match req.method.as_str() {
        GotoDefinition::METHOD => {
            send_ok(
                conn,
                req.id.clone(),
                &lsp_types::GotoDefinitionResponse::Array(Vec::new()),
            )?;
        }
        Completion::METHOD => {
            let p: CompletionParams = serde_json::from_value(req.params.clone())?;

            let doc = docs
                .get(&p.text_document_position.text_document.uri)
                .ok_or("Completion Request in unknown document")?;

            let Some(ast) = &*doc.typed_ast.borrow_mut() else {
                send_err(
                    conn,
                    req.id.clone(),
                    lsp_server::ErrorCode::RequestFailed,
                    "AST not avaible due to syntax error",
                )?;
                return Ok(());
            };

            // let (line, col) = lsp_position_to_pest_position(p.text_document_position.position);
            // let node = ast::nearest_node(ast.parsed(), line, col);

            let type_checker = ast.type_checker();
            let mut items = vec![];

            for scope in &type_checker.scope_stack {
                for (function_name, signature) in &scope.functions {
                    let hint_full = signature.lsp_render_full(*function_name);
                    let hint_short = signature.lsp_render_short(*function_name);

                    items.push(CompletionItem {
                        label: (*function_name).into(),
                        label_details: Some(CompletionItemLabelDetails {
                            detail: Some(cleanup_whitespace(&hint_short).into()),
                            description: None,
                        }),
                        kind: Some(CompletionItemKind::FUNCTION),
                        documentation: Some(Documentation::MarkupContent(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: format!("```c\n{hint_full}\n```"),
                        })),
                        ..Default::default()
                    })
                }

                for (var_name, var_version) in &scope.variables {
                    let Some((_, var_type, kind)) = scope.variables_versioned.get(var_version)
                    else {
                        continue;
                    };

                    let lsp_kind = match kind {
                        VariableKind::Local => CompletionItemKind::VARIABLE,
                        VariableKind::Constant => CompletionItemKind::CONSTANT,
                        VariableKind::Capture(_) => CompletionItemKind::REFERENCE,
                    };

                    items.push(CompletionItem {
                        label: (*var_name).into(),
                        label_details: Some(CompletionItemLabelDetails {
                            detail: Some(cleanup_whitespace(&format!("{var_type}")).into()),
                            description: None,
                        }),
                        kind: Some(lsp_kind),
                        documentation: Some(Documentation::MarkupContent(MarkupContent {
                            kind: MarkupKind::Markdown,
                            value: format!("```c\n{var_type} {var_name} // {kind:?}\n```"),
                        })),
                        ..Default::default()
                    })
                }
            }

            for (typedef_name, typedef_type) in &type_checker.typedefs {
                let hint = format!("typedef {typedef_type} {typedef_name}");

                items.push(CompletionItem {
                    label: (*typedef_name).into(),
                    label_details: Some(CompletionItemLabelDetails {
                        detail: Some(cleanup_whitespace(&hint).into()),
                        description: None,
                    }),
                    kind: Some(CompletionItemKind::STRUCT),
                    documentation: Some(Documentation::MarkupContent(MarkupContent {
                        kind: MarkupKind::Markdown,
                        value: format!("```c\n{hint}\n```"),
                    })),
                    ..Default::default()
                })
            }

            send_ok(conn, req.id.clone(), &CompletionResponse::Array(items))?;
        }
        HoverRequest::METHOD => {
            let p: HoverParams = serde_json::from_value(req.params.clone())?;

            let doc = docs
                .get(&p.text_document_position_params.text_document.uri)
                .ok_or("Hover Request in unknown document")?;

            let Some(ast) = &*doc.parsed_ast.borrow_mut() else {
                send_err(
                    conn,
                    req.id.clone(),
                    lsp_server::ErrorCode::RequestFailed,
                    "AST not avaible due to syntax error",
                )?;
                return Ok(());
            };

            let (line, col) =
                lsp_position_to_pest_position(p.text_document_position_params.position);

            let node = ast::nearest_node(ast.parsed(), line, col);

            let mut str = String::new();
            write!(&mut str, "{:#?}", node.as_ast_node())?;

            let hover = Hover {
                contents: HoverContents::Scalar(MarkedString::String(str)),
                range: None,
            };
            send_ok(conn, req.id.clone(), &hover)?;
        }
        WorkspaceDiagnosticRefresh::METHOD => {
            let file_cache = make_file_cache(docs);
            for doc in docs.values() {
                build_asts_and_send_diagnostics(conn, doc, &file_cache)?;
            }
        }
        // Formatting::METHOD => {
        //     let p: DocumentFormattingParams = serde_json::from_value(req.params.clone())?;
        //     let uri = p.text_document.uri;
        //     let text = docs
        //         .get(&uri)
        //         .ok_or_else(|| anyhow!("document not in cache – did you send DidOpen?"))?;
        //     let formatted = run_rustfmt(text)?;
        //     let edit = TextEdit {
        //         range: full_range(text),
        //         new_text: formatted,
        //     };
        //     send_ok(conn, req.id.clone(), &vec![edit])?;
        // }
        _ => send_err(
            conn,
            req.id.clone(),
            lsp_server::ErrorCode::MethodNotFound,
            "unhandled method",
        )?,
    }
    Ok(())
}

// =====================================================================
// helpers
// =====================================================================

fn cleanup_whitespace(str: &str) -> Cow<'_, str> {
    static REGEX: LazyLock<Regex> = LazyLock::new(|| Regex::new(r"\s+").unwrap());

    REGEX.replace_all(str, " ")
}

fn make_file_cache(docs: &DocumentMap) -> FileCache<'_> {
    docs.into_iter()
        .map(|(uri, doc)| (uri.path().as_str().as_ref(), doc.contents.as_ref()))
        .collect()
}

fn build_asts_and_send_diagnostics(
    conn: &Connection,
    doc: &Document,
    file_cache: &FileCache,
) -> Result<()> {
    let res = try {
        let parsed_ast = CachedParsedAst::new(
            doc.file_name.clone(),
            doc.contents.clone(),
            |file_name, contents| parse_ast(file_name, contents),
        )?;
        *doc.parsed_ast.borrow_mut() = Some(parsed_ast);

        let ctx = CompileContext::new(&*doc.file_name, file_cache, CompileConfig::default());
        let ctx = match ctx {
            Ok(ctx) => Ok(Rc::new(ctx)),
            Err(err) => Err(vec![Diagnostic {
                range: first_line(&doc.contents),
                severity: Some(DiagnosticSeverity::ERROR),
                code: Some(NumberOrString::String(
                    "Could not collect imports".to_string(),
                )),
                code_description: None,
                source: Some("flap-ls".to_string()),
                message: format!("{err}"),
                related_information: None,
                tags: None,
                data: None,
            }]),
        }?;

        let (typed_ast, diagnostics) = CachedTypedAst::new(ctx.clone(), |ctx| type_check(ctx));
        *doc.typed_ast.borrow_mut() = Some(typed_ast);

        if !diagnostics.is_empty() {
            Err(diagnostics)?;
        }

        full_run(&ctx)?;
    };

    match res {
        Ok(()) => send_diagnostics(conn, vec![], doc),
        Err(diags) => send_diagnostics(conn, diags, doc),
    }
}

fn send_diagnostics(conn: &Connection, diags: Vec<Diagnostic>, doc: &Document) -> Result<()> {
    let params = PublishDiagnosticsParams {
        uri: doc.uri.clone(),
        diagnostics: diags,
        version: Some(doc.version),
    };
    conn.sender
        .send(Message::Notification(lsp_server::Notification::new(
            PublishDiagnostics::METHOD.to_owned(),
            params,
        )))?;

    Ok(())
}

fn parse_ast<'a>(file_name: &'a str, contents: &'a str) -> Result<Program<'a>, Vec<Diagnostic>> {
    let res = parser::parse_program(contents, file_name)
        .map_err(|err| parser::map_parser_error(err, file_name, contents));

    match res {
        Ok(prog) => Ok(prog),
        Err(err) => Err(vec![diagnostic_for_error(&err, file_name)]),
    }
}

fn type_check<'a>(ctx: &'a CompileContext) -> (TypeChecker<'a>, Block<'a>, Vec<Diagnostic>) {
    let mut segments = ctx.collect_segments();
    let mut type_checker = TypeChecker::default();
    let mut statements = Vec::new();
    let mut diagnostics = Vec::new();

    for segment in &mut segments {
        match &mut segment.ast {
            Ok(program) => {
                for statement in &mut program.code.statements {
                    let res = statement.check_and_resolve_types(&mut type_checker);

                    match res {
                        Ok(_type) => {}
                        Err(err) => {
                            diagnostics.push(diagnostic_for_error(&err, &ctx.root().file_name))
                        }
                    }
                }

                statements.extend(program.code.statements.drain(..));
            }
            Err(err) => diagnostics.push(diagnostic_for_error(err, &ctx.root().file_name)),
        }
    }

    (
        type_checker,
        Block {
            statements,
            captures: Default::default(),
            span: AnnotatedSpan {
                span: Span::new("<merged sources>", 0, 16).unwrap(),
                file_name: "<merged sources>",
            },
        },
        diagnostics,
    )
}

fn full_run(ctx: &CompileContext) -> Result<(), Vec<Diagnostic>> {
    let res = compile::compile(ctx);

    match res {
        Ok(_) => Ok(()),
        Err(err) => Err(vec![diagnostic_for_error(&err, &ctx.root().file_name)]),
    }
}

fn diagnostic_for_error(error: &impl IntoSpans, main_path: &str) -> Diagnostic {
    let error_kind = error.error_kind();
    let mut spans = error
        .spans()
        .map(|(span, desc)| (span_to_location(span), desc));

    let (main, desc) = spans.next().unwrap_or_else(|| {
        (
            Location {
                range: first_char(),
                uri: make_uri_for_path(main_path),
            },
            None,
        )
    });

    let message = match desc {
        Some(desc) => format!("{desc}\n{error}"),
        None => format!("{error}"),
    };

    let mut related_info = Vec::new();
    for (location, desc) in spans {
        let message = match desc {
            Some(desc) => desc.to_string(),
            None => message.clone(),
        };

        related_info.push(DiagnosticRelatedInformation { location, message });
    }

    Diagnostic {
        range: main.range,
        severity: Some(DiagnosticSeverity::ERROR),
        code: Some(NumberOrString::String(error_kind.to_string())),
        code_description: None,
        source: Some("flap-ls".to_string()),
        message,
        related_information: Some(related_info),
        tags: None,
        data: None,
    }
}

fn full_range(text: &str) -> Range {
    let last_line_idx = text.lines().count().saturating_sub(1) as u32;
    let last_col = text.lines().last().map_or(0, |l| l.chars().count()) as u32;
    Range::new(Position::new(0, 0), Position::new(last_line_idx, last_col))
}

fn first_line(text: &str) -> Range {
    let last_col = text.lines().next().map_or(1, |l| l.chars().count()) as u32;

    Range::new(Position::new(0, 0), Position::new(0, last_col))
}

fn first_char() -> Range {
    Range::new(Position::new(0, 0), Position::new(0, 1))
}

fn send_ok<T: serde::Serialize>(conn: &Connection, id: RequestId, result: &T) -> Result<()> {
    let resp = Response {
        id,
        result: Some(serde_json::to_value(result)?),
        error: None,
    };
    conn.sender.send(Message::Response(resp))?;
    Ok(())
}

fn send_err(
    conn: &Connection,
    id: RequestId,
    code: lsp_server::ErrorCode,
    msg: &str,
) -> Result<()> {
    let resp = Response {
        id,
        result: None,
        error: Some(lsp_server::ResponseError {
            code: code as i32,
            message: msg.into(),
            data: None,
        }),
    };
    conn.sender.send(Message::Response(resp))?;
    Ok(())
}

fn make_uri_for_path(path: &str) -> Uri {
    format!("file://{path}").parse().unwrap()
}

fn span_to_location(span: AnnotatedSpan) -> lsp_types::Location {
    let (start, end) = span.span.split();
    let start = pest_position_to_lsp_position(start.line_col());
    let end = pest_position_to_lsp_position(end.line_col());

    Location {
        range: Range::new(start, end),
        uri: make_uri_for_path(span.file_name),
    }
}

fn pest_position_to_lsp_position(pos: (usize, usize)) -> lsp_types::Position {
    let (line, col) = pos;

    lsp_types::Position::new(line as u32 - 1, col as u32 - 1)
}

fn lsp_position_to_pest_position(pos: lsp_types::Position) -> (usize, usize) {
    (pos.line as usize + 1, pos.character as usize + 1)
}
