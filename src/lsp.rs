use std::collections::HashMap;
use std::fmt::Write as _;
use std::path::Path;
use std::usize;
use std::{error::Error, io::Write};

use std::process::Stdio;

use color_eyre::Result;
use color_eyre::eyre::{Context, ContextCompat};
use lsp_server::{Connection, Message, Request as ServerRequest, RequestId, Response};
use lsp_types::notification::Notification as _; // for METHOD consts
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
    DocumentFormattingParams,
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
    TextEdit,
    Uri,
    // notifications
    notification::{DidChangeTextDocument, DidOpenTextDocument, PublishDiagnostics},
    // requests
    request::{Completion, Formatting, GotoDefinition, HoverRequest},
};
use lsp_types::{DiagnosticRelatedInformation, HoverParams, Location, NumberOrString};
use pest::Span;
use pest::error::LineColLocation;
use tracing::{error, info};

use crate::ast::{self, AnnotatedSpan, Block, Program};
use crate::compile::{self, CompileConfig, CompileContext, CompileError, FileCache};
use crate::parser;
use crate::type_check::{TypeCheck, TypeChecker};

#[derive(Debug, Clone)]
struct Document {
    uri: Uri,
    contents: String,
    version: i32,
}

pub fn start_lsp() -> Result<()> {
    info!("starting flap-ls");

    // transport
    let (connection, io_thread) = Connection::stdio();

    // advertised capabilities
    let caps = ServerCapabilities {
        text_document_sync: Some(TextDocumentSyncCapability::Kind(TextDocumentSyncKind::FULL)),
        completion_provider: Some(CompletionOptions::default()),
        definition_provider: Some(OneOf::Left(true)),
        hover_provider: Some(HoverProviderCapability::Simple(true)),
        document_formatting_provider: Some(OneOf::Left(false)),
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
    let mut docs: HashMap<Uri, Document> = HashMap::default();

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
    docs: &mut HashMap<Uri, Document>,
) -> Result<()> {
    match note.method.as_str() {
        DidOpenTextDocument::METHOD => {
            let p: DidOpenTextDocumentParams = serde_json::from_value(note.params.clone())?;
            let doc = Document {
                uri: p.text_document.uri,
                contents: p.text_document.text,
                version: p.text_document.version,
            };

            docs.insert(doc.uri.clone(), doc.clone());

            let file_cache = make_file_cache(docs);
            compute_and_send_diagnostics(conn, &doc, &file_cache)?;
        }
        DidChangeTextDocument::METHOD => {
            let p: DidChangeTextDocumentParams = serde_json::from_value(note.params.clone())?;
            if let Some(change) = p.content_changes.into_iter().next() {
                let doc = Document {
                    uri: p.text_document.uri,
                    contents: change.text,
                    version: p.text_document.version,
                };

                docs.insert(doc.uri.clone(), doc.clone());

                let file_cache = make_file_cache(docs);
                compute_and_send_diagnostics(conn, &doc, &file_cache)?;
            }
        }
        _ => {}
    }
    Ok(())
}

// =====================================================================
// requests
// =====================================================================

fn handle_request(
    conn: &Connection,
    req: &ServerRequest,
    docs: &mut HashMap<Uri, Document>,
) -> Result<()> {
    match req.method.as_str() {
        GotoDefinition::METHOD => {
            send_ok(
                conn,
                req.id.clone(),
                &lsp_types::GotoDefinitionResponse::Array(Vec::new()),
            )?;
        }
        Completion::METHOD => {
            let item = CompletionItem {
                label: "HelloFromLSP".into(),
                kind: Some(CompletionItemKind::FUNCTION),
                detail: Some("dummy completion".into()),
                ..Default::default()
            };
            send_ok(conn, req.id.clone(), &CompletionResponse::Array(vec![item]))?;
        }
        HoverRequest::METHOD => {
            let p: HoverParams = serde_json::from_value(req.params.clone())?;

            let doc = docs
                .get(&p.text_document_position_params.text_document.uri)
                .wrap_err("Hover Request in unknown document")?;
            let Ok(ast) = parse_ast(&doc) else {
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

            let node = ast::nearest_node(&ast, line, col);

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
                compute_and_send_diagnostics(conn, doc, &file_cache)?;
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

fn make_file_cache(docs: &HashMap<Uri, Document>) -> FileCache<'_> {
    docs.into_iter()
        .map(|(uri, doc)| (uri.as_str().as_ref(), doc.contents.as_ref()))
        .collect()
}

fn compute_and_send_diagnostics(
    conn: &Connection,
    doc: &Document,
    file_cache: &FileCache,
) -> Result<()> {
    let res = parse_ast(&doc).and_then(|_| full_run(&doc, file_cache));
    match res {
        Ok(_) => {
            send_diagnostics(conn, vec![], &doc)?;
        }
        Err(diag) => {
            send_diagnostics(conn, vec![diag], &doc)?;
        }
    }

    Ok(())
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

fn parse_ast(doc: &Document) -> Result<Program<'_>, Diagnostic> {
    let file_name = doc.uri.path().as_str();
    let res = parser::parse_program(&doc.contents, file_name)
        .map_err(|err| parser::map_parser_error(err, file_name, &doc.contents));

    match res {
        Ok(prog) => Ok(prog),
        Err(err) => {
            let range = match err.line_col {
                LineColLocation::Pos(start) => Range::new(
                    pest_position_to_lsp_position(start),
                    pest_position_to_lsp_position(start),
                ),
                LineColLocation::Span(start, end) => Range::new(
                    pest_position_to_lsp_position(start),
                    pest_position_to_lsp_position(end),
                ),
            };

            Err(Diagnostic {
                range,
                severity: Some(DiagnosticSeverity::ERROR),
                code: Some(NumberOrString::String("Syntax Error".to_string())),
                code_description: None,
                source: Some("flap-ls".to_string()),
                message: format!("{err}"),
                related_information: None,
                tags: None,
                data: None,
            })
        }
    }
}

fn check_imports_fine_grained<'a>(
    ctx: &'a CompileContext,
) -> (Option<(Block<'a>, TypeChecker<'a>)>, Vec<Diagnostic>) {
    // let file_name = doc.uri.path().as_str();
    // let ctx = CompileContext::new(file_name, file_cache);
    //
    // let ctx = match ctx {
    //     Ok(ctx) => ctx,
    //     Err(err) => {
    //         // TODO: make this failure mode fine grained too
    //         return (
    //             None,
    //             vec![Diagnostic {
    //                 range: full_range(&doc.contents),
    //                 severity: Some(DiagnosticSeverity::ERROR),
    //                 code: Some(NumberOrString::String(
    //                     "Could not create compile context".to_string(),
    //                 )),
    //                 code_description: None,
    //                 source: Some("flap-ls".to_string()),
    //                 message: format!("{err:?}"),
    //                 related_information: None,
    //                 tags: None,
    //                 data: None,
    //             }],
    //         );
    //     }
    // };

    let mut segments = ctx.collect_segments();
    let mut type_checker = TypeChecker::default();
    let mut statements = Vec::new();
    let mut diagnostics = Vec::new();

    for segment in &mut segments {
        let range = match segment.path.last() {
            Some(import) => Range::new(
                pest_position_to_lsp_position(import.start),
                pest_position_to_lsp_position(import.end),
            ),
            None => full_range(&ctx.root().contents),
        };

        match &mut segment.ast {
            Ok(program) => {
                let checkpoint = type_checker.clone();
                let res = program.code.check_and_resolve_types(&mut type_checker);
                match res {
                    Ok(_type) => {
                        statements.extend(program.code.statements.drain(..));
                    }
                    Err(err) => {
                        type_checker = checkpoint;

                        diagnostics.push(Diagnostic {
                            range,
                            severity: Some(DiagnosticSeverity::ERROR),
                            code: Some(NumberOrString::String("Type Check Failed".to_string())),
                            code_description: None,
                            source: Some("flap-ls".to_string()),
                            message: format!("{err:?}"),
                            related_information: None,
                            tags: None,
                            data: None,
                        })
                    }
                }
            }
            Err(err) => match err {
                CompileError::Parsing(err) => {
                    let mut related_information = vec![];
                    if let Some(path) = err.path() {
                        let range = match err.line_col {
                            LineColLocation::Pos(start) => Range::new(
                                pest_position_to_lsp_position(start),
                                pest_position_to_lsp_position(start),
                            ),
                            LineColLocation::Span(start, end) => Range::new(
                                pest_position_to_lsp_position(start),
                                pest_position_to_lsp_position(end),
                            ),
                        };

                        related_information.push(DiagnosticRelatedInformation {
                            location: Location {
                                uri: format!("file://{}", path).parse().expect("Build uri"),
                                range,
                            },
                            message: format!("{err}"),
                        });
                    }

                    diagnostics.push(Diagnostic {
                        range,
                        severity: Some(DiagnosticSeverity::ERROR),
                        code: Some(NumberOrString::String(
                            "Syntax Error in imported file".to_string(),
                        )),
                        code_description: None,
                        source: Some("flap-ls".to_string()),
                        message: format!("{err}"),
                        related_information: Some(related_information),
                        tags: None,
                        data: None,
                    });
                }
                err => diagnostics.push(Diagnostic {
                    range,
                    severity: Some(DiagnosticSeverity::ERROR),
                    code: Some(NumberOrString::String("Unknown Error".to_string())),
                    code_description: None,
                    source: Some("flap-ls".to_string()),
                    message: format!("{err:?}"),
                    related_information: None,
                    tags: None,
                    data: None,
                }),
            },
        }
    }

    (
        Some((
            Block {
                statements,
                captures: Default::default(),
                span: AnnotatedSpan {
                    span: Span::new("<merged sources>", 0, 16).unwrap(),
                    file_name: "<merged sources>",
                },
            },
            type_checker,
        )),
        diagnostics,
    )
}

fn full_run(doc: &Document, file_cache: &FileCache) -> Result<(), Diagnostic> {
    let file = doc.uri.path().as_str();
    let res = compile::compile(file, CompileConfig::default(), file_cache);

    match res {
        Ok(_) => Ok(()),
        Err(err) => Err(Diagnostic {
            range: full_range(&doc.contents),
            severity: Some(DiagnosticSeverity::ERROR),
            code: Some(NumberOrString::String("Compile fail".to_string())),
            code_description: None,
            source: Some("flap-ls".to_string()),
            message: format!("{err:?}"),
            related_information: None,
            tags: None,
            data: None,
        }),
    }
}

fn full_range(text: &str) -> Range {
    let last_line_idx = text.lines().count().saturating_sub(1) as u32;
    let last_col = text.lines().last().map_or(0, |l| l.chars().count()) as u32;
    Range::new(Position::new(0, 0), Position::new(last_line_idx, last_col))
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

fn pest_position_to_lsp_position(pos: (usize, usize)) -> lsp_types::Position {
    let (line, col) = pos;

    lsp_types::Position::new(line as u32 - 1, col as u32 - 1)
}

fn lsp_position_to_pest_position(pos: lsp_types::Position) -> (usize, usize) {
    (pos.line as usize + 1, pos.character as usize + 1)
}
