//! `isle-trace-oracle <file.clif>`: compile every function for `aarch64-unknown-linux-gnu`
//! with the `clif2obj` settings (`opt_level=none`, verifier, regalloc checker, PIC) using a
//! `trace-log` build of cranelift-codegen 0.136.1, and print the ISLE rules fired, one per line:
//! `ISLE <term> <file> line <0-based line>` (the generated code's own log format), preceded by
//! `function <name>`.

use anyhow::{Context as _, Result, anyhow};
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable};
use std::str::FromStr;

struct Tracer;

impl log::Log for Tracer {
    fn enabled(&self, m: &log::Metadata) -> bool {
        m.level() <= log::Level::Debug
    }
    fn log(&self, r: &log::Record) {
        let msg = r.args().to_string();
        if msg.starts_with("ISLE ") {
            println!("{msg}");
        }
    }
    fn flush(&self) {}
}

static TRACER: Tracer = Tracer;

fn main() -> Result<()> {
    let path = std::env::args().nth(1).context("usage: isle-trace-oracle <file.clif>")?;
    let src = std::fs::read_to_string(&path).with_context(|| format!("reading {path}"))?;
    log::set_logger(&TRACER).map_err(|e| anyhow!("{e}"))?;
    log::set_max_level(log::LevelFilter::Debug);

    let mut flags = settings::builder();
    for (k, v) in [
        ("opt_level", "none"),
        ("enable_verifier", "true"),
        ("regalloc_checker", "true"),
        ("is_pic", "true"),
    ] {
        flags.set(k, v)?;
    }
    let triple = target_lexicon::Triple::from_str("aarch64-unknown-linux-gnu").map_err(|e| anyhow!("{e}"))?;
    let isa = isa::lookup(triple)?.finish(settings::Flags::new(flags))?;

    let funcs = cranelift_reader::parse_functions(&src).map_err(|e| anyhow!("{e}"))?;
    for f in funcs {
        println!("function {}", f.name);
        let mut ctx = cranelift_codegen::Context::for_function(f);
        ctx.compile(&*isa, &mut cranelift_control::ControlPlane::default())
            .map_err(|e| anyhow!("{e:?}"))?;
    }
    Ok(())
}
