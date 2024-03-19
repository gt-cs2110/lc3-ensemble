use std::borrow::Cow;
use std::ops::Range;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use ariadne::{ColorGenerator, Label, Report, ReportKind, Source};
use clap::{Parser, Subcommand};
use lc3_ensemble::asm::assemble;
use lc3_ensemble::err::ErrSpan;
use lc3_ensemble::parse::parse_ast;

#[derive(Parser)]
#[command(version, about, long_about = None)]
struct Args {
    #[command(subcommand)]
    cmd: Command
}
#[derive(Subcommand)]
enum Command {
    Assemble {
        input: PathBuf,
        #[arg(short, long)]
        output: Option<PathBuf>
    },
    Run {
        input: PathBuf,
    },
    Debug {
        input: PathBuf,
    }
}

struct SourceMetadata<'fp> {
    name: Cow<'fp, str>,
    src: Source<String>
}

fn main() -> ExitCode {
    let Args { cmd } = Args::parse();

    let result = match cmd {
        Command::Assemble { input, output } => cmd_assemble(&input, output.as_deref().unwrap_or(&input)),
        Command::Run { input } => cmd_run(&input),
        Command::Debug { input } => cmd_debug(&input),
    };

    match result {
        Ok(_)  => ExitCode::SUCCESS,
        Err(e) => e,
    }
}

fn cmd_assemble(input: &Path, output: &Path) -> Result<(), ExitCode> {
    let src = handle_read(input, std::fs::read_to_string)?;

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
                    return Err(ExitCode::FAILURE);
                }
            }
        }
    }

    let ast = handle!(parse_ast(&src));
    let obj = handle!(assemble(ast));
    
    Ok(())
}
fn cmd_run(input: &Path) -> Result<(), ExitCode> {
    Err(ExitCode::FAILURE)
}
fn cmd_debug(input: &Path) -> Result<(), ExitCode> {
    Err(ExitCode::FAILURE)
}

fn handle_read<'p, T>(input: &'p Path, read: impl FnOnce(&'p Path) -> std::io::Result<T>) -> Result<T, ExitCode> {
    read(input)
        .map_err(|e| {
            Report::<Range<_>>::build(ReportKind::Error, (), 0)
                .with_message(format!("{}: {e}", input.display()))
                .finish()
                .eprint(Source::from(""))
                .unwrap();
            
            ExitCode::FAILURE
        })
}
fn report_error<E: lc3_ensemble::err::Error>(err: E, meta: &SourceMetadata) -> std::io::Result<()> {
    let mut colors = ColorGenerator::new();

    match err.span() {
        Some(span) => {
            let mut report = Report::build(ReportKind::Error, &*meta.name, span.first().start)
                .with_message(&err);

            match span {
                ErrSpan::One(r) => {
                    report = report.with_label({
                        let mut label = Label::new((&*meta.name, r))
                            .with_color(colors.next());
                        
                        if let Some(help) = err.help() {
                            label = label.with_message(help);
                        }
    
                        label
                    });
                },
                ErrSpan::Two([r0, r1]) => {
                    report = report
                        .with_label({
                            Label::new((&*meta.name, r0))
                                    .with_color(colors.next())
                                    .with_message("")
                        })
                        .with_label({
                            Label::new((&*meta.name, r1))
                                    .with_color(colors.next())
                                    .with_message("")
                        });

                    if let Some(help) = err.help() {
                        report.set_help(help);
                    }
                },
                ErrSpan::Many(mr) => {
                    report = report.with_labels({
                        mr.into_iter()
                            .map(|s| {
                                Label::new((&*meta.name, s.clone()))
                                    .with_color(colors.next())
                                    .with_message("")
                            })
                    });

                    if let Some(help) = err.help() {
                        report.set_help(help);
                    }
                },
            }
            
            report
                .finish()
                .eprint((&*meta.name, meta.src.clone()))
        },
        None => {
            let mut report = Report::build(ReportKind::Error, &*meta.name, 0)
                .with_message(&err);
            
            if let Some(help) = err.help() {
                report = report
                    .with_label(Label::new((&*meta.name, 0..0)))
                    .with_help(help)
            };

            report
                .finish()
                .eprint((&*meta.name, Source::from("")))
        },
    }
}