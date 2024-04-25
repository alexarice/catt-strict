use ropey::Rope;
use tower_lsp::{jsonrpc::Result, lsp_types::*, Client, LanguageServer};

use crate::{
    command::{run_import, CattError},
    common::Signature,
};

#[derive(Debug)]
pub struct Backend {
    pub client: Client,
    pub env: Signature,
}

#[tower_lsp::async_trait]
impl LanguageServer for Backend {
    async fn initialize(&self, _: InitializeParams) -> Result<InitializeResult> {
        Ok(InitializeResult {
            capabilities: ServerCapabilities {
                text_document_sync: Some(TextDocumentSyncCapability::Kind(
                    TextDocumentSyncKind::FULL,
                )),
                ..Default::default()
            },
            ..Default::default()
        })
    }

    async fn initialized(&self, _: InitializedParams) {
        self.client
            .log_message(MessageType::INFO, "server initialized! version 4")
            .await;
    }

    async fn shutdown(&self) -> Result<()> {
        Ok(())
    }

    async fn did_open(&self, params: DidOpenTextDocumentParams) {
        self.client
            .log_message(MessageType::INFO, "file opened!")
            .await;
        self.on_change(params.text_document.uri, params.text_document.text)
            .await
    }

    async fn did_change(&self, params: DidChangeTextDocumentParams) {
        self.client
            .log_message(
                MessageType::INFO,
                format!("file changed {}", &params.text_document.uri),
            )
            .await;
        self.on_change(
            params.text_document.uri,
            params.content_changes.into_iter().next().unwrap().text,
        )
        .await
    }
}

impl CattError {
    pub fn to_diag(self, rope: &Rope) -> Vec<Diagnostic> {
        match self {
            CattError::ParseError(es) => es
                .into_iter()
                .map(|e| {
                    let sp = e.span();
                    let start = offset_to_position(sp.start, rope).unwrap();
                    let end = offset_to_position(sp.end, rope).unwrap();
                    Diagnostic::new_simple(Range { start, end }, e.to_string())
                })
                .collect(),
            e => {
                let sp = e.span();
                let start = offset_to_position(sp.start, rope).unwrap();
                let end = offset_to_position(sp.end, rope).unwrap();
                vec![Diagnostic::new_simple(Range { start, end }, e.to_string())]
            }
        }
    }
}

impl Backend {
    async fn on_change(&self, uri: Url, text: String) {
        let rope = Rope::from_str(&text);
        if let Ok(import_file) = uri.to_file_path() {
            if let Err(e) = run_import(&import_file, &mut self.env.clone(), text, false) {
                self.client
                    .publish_diagnostics(uri, e.to_diag(&rope), None)
                    .await
            }
        } else {
            self.client
                .log_message(MessageType::ERROR, "Could not parse uri")
                .await
        }
    }
}

fn offset_to_position(offset: usize, rope: &Rope) -> Option<Position> {
    let line = rope.try_char_to_line(offset).ok()?;
    let first_char_of_line = rope.try_line_to_char(line).ok()?;
    let column = offset - first_char_of_line;
    Some(Position::new(line as u32, column as u32))
}
