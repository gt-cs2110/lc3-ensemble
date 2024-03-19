use std::borrow::Cow;
use std::ops::Range;
use std::path::PathBuf;
use std::process::ExitCode;

use ariadne::{Color, ColorGenerator, Config, FileCache, Fmt, Label, Report, ReportKind, Source};
use clap::Parser;
use lc3_ensemble::parse::parse_ast;

#[derive(Parser)]
struct Args {
    #[arg(short, long)]
    input: PathBuf,
    #[arg(short, long)]
    output: Option<PathBuf>
}

struct SourceMetadata<'fp> {
    name: Cow<'fp, str>,
    src: Source<String>
}
fn main() -> ExitCode {
    let Args { input, output } = Args::parse();

    let src = match std::fs::read_to_string(&input) {
        Ok(s) => s,
        Err(e) => {
            Report::<Range<_>>::build(ReportKind::Error, (), 0)
                .with_message(format!("{}: {e}", input.display()))
                .finish()
                .eprint(Source::from(""))
                .unwrap();
            return ExitCode::FAILURE;
        }
    };


    let meta = SourceMetadata {
        name: input.to_string_lossy(),
        src: Source::from(src.clone())
    };
    macro_rules! handle {
        ($e:expr) => {
            match $e {
                Ok(t) => t,
                Err(e) => {
                    report_error(e, &meta).unwrap();
                    return ExitCode::FAILURE;
                }
            }
        }
    }

    let ast = handle!(parse_ast(&src));

    // assemble(ast)
    ExitCode::SUCCESS
}

fn report_error<E: lc3_ensemble::err::Error>(err: E, meta: &SourceMetadata) -> std::io::Result<()> {
    let mut colors = ColorGenerator::new();

    match err.span() {
        Some(span) => {
            Report::build(ReportKind::Error, &*meta.name, span.clone().start)
                .with_message(&err)
                .with_label({
                    let mut label = Label::new((&*meta.name, span.clone()))
                        .with_color(colors.next());
                    
                    if let Some(help) = err.help() {
                        label = label.with_message(help);
                    }

                    label
                })
                .finish()
                .eprint((&*meta.name, meta.src.clone()))
        },
        None => {
            let mut report = Report::<Range<_>>::build(ReportKind::Error, (), 0)
                .with_message(&err);
            
            if let Some(help) = err.help() {
                report.set_help(help);
            }

            report.finish()
                .eprint(Source::from(""))
        },
    }
}