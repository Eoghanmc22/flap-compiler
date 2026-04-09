use std::collections::HashMap;
use std::fmt::Write as _;
use std::usize;
use std::{error::Error, io::Write};

use std::process::Stdio;

use color_eyre::Result;
use color_eyre::eyre::ContextCompat;
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
use lsp_types::{HoverParams, NumberOrString};
use pest::error::LineColLocation;
use tracing::{error, info};

use crate::ast::{self, Program};
use crate::parser;

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

            let ast = make_ast(&doc);
            match ast {
                Ok(_) => {
                    send_diagnostics(conn, vec![], &doc)?;
                }
                Err(diag) => {
                    send_diagnostics(conn, vec![diag], &doc)?;
                }
            }

            docs.insert(doc.uri.clone(), doc);
        }
        DidChangeTextDocument::METHOD => {
            let p: DidChangeTextDocumentParams = serde_json::from_value(note.params.clone())?;
            if let Some(change) = p.content_changes.into_iter().next() {
                let doc = Document {
                    uri: p.text_document.uri,
                    contents: change.text,
                    version: p.text_document.version,
                };

                let ast = make_ast(&doc);
                match ast {
                    Ok(_) => {
                        send_diagnostics(conn, vec![], &doc)?;
                    }
                    Err(diag) => {
                        send_diagnostics(conn, vec![diag], &doc)?;
                    }
                }

                docs.insert(doc.uri.clone(), doc);
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
            let Ok(ast) = make_ast(&doc) else {
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
            for doc in docs.values() {
                let ast = make_ast(&doc);
                match ast {
                    Ok(_) => {
                        send_diagnostics(conn, vec![], &doc)?;
                    }
                    Err(diag) => {
                        send_diagnostics(conn, vec![diag], &doc)?;
                    }
                }
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

fn make_ast(doc: &Document) -> Result<Program<'_>, Diagnostic> {
    let res = parser::parse_program(&doc.contents)
        .map_err(|err| parser::map_parser_error(err, None, &doc.contents));

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
