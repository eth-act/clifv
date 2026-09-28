//! `isle-trace-oracle <file.clif>`: compile every function for `aarch64-unknown-linux-gnu`
//! with the `clif2obj` settings (`opt_level=none`, verifier, regalloc checker, PIC) using a
//! `trace-log` build of cranelift-codegen 0.136.1, and print the ISLE rules fired, one per line:
//! `ISLE <term> <file> line <0-based line>` (the generated code's own log format), preceded by
//! `function <name>`.
//!
//! `isle-trace-oracle --opt <file.clif>`: the same with `opt_level=speed`, printing one line
//! per call of the mid-end's `simplify` (in completion order, so nested calls from `make_inst`
//! come before the call that caused them):
//! `simplify vN: <file>:<1-based line> ... -> [results]`, where the rules are the `simplify`
//! rules that contributed a result to this call (in the generated code's order) and the
//! results are the call's values after Cranelift's shuffle, `MATCHES_LIMIT` truncation, sort
//! and dedup (`egraph/mod.rs` `optimize_pure_enode`); and one line per call of
//! `simplify_skeleton` (every side-effecting instruction and terminator, in the order the
//! e-graph pass visits them): `simplify_skeleton: <file>:<line> ... -> <number of results>`.

use anyhow::{Context as _, Result, anyhow};
use cranelift_codegen::isa;
use cranelift_codegen::settings::{self, Configurable};
use std::str::FromStr;
use std::cell::RefCell;

struct Tracer;

/// Open `simplify` calls (value, rules fired so far), and the `simplify_skeleton` rules fired
/// in the current skeleton call.
#[derive(Default)]
struct OptState {
    stack: Vec<(String, Vec<String>)>,
    skeleton: Vec<String>,
}

/// `<file> line <0-based>` as `<file>:<1-based>`.
fn loc(rest: &str) -> Option<String> {
    let (file, line) = rest.split_once(" line ")?;
    let n: usize = line.trim().parse().ok()?;
    Some(format!("{file}:{}", n + 1))
}

thread_local! {
    /// `--opt` mode state. Compilation logs from the main thread only.
    static OPT: RefCell<Option<OptState>> = const { RefCell::new(None) };
}

impl log::Log for Tracer {
    fn enabled(&self, m: &log::Metadata) -> bool {
        m.level() <= log::Level::Trace
    }
    fn log(&self, r: &log::Record) {
        let msg = r.args().to_string();
        OPT.with_borrow_mut(|opt| Self::record(opt, r.level(), &msg));
    }
    fn flush(&self) {}
}

impl Tracer {
    fn record(opt: &mut Option<OptState>, level: log::Level, msg: &str) {
        let Some(OptState { stack, skeleton }) = opt.as_mut() else {
            if level <= log::Level::Debug && msg.starts_with("ISLE ") {
                println!("{msg}");
            }
            return;
        };
        if let Some(v) = msg.strip_prefix("Calling into ISLE with original value ") {
            stack.push((v.to_string(), Vec::new()));
        } else if let Some(rest) = msg.strip_prefix("ISLE simplify ") {
            if let (Some(top), Some(l)) = (stack.last_mut(), loc(rest)) {
                top.1.push(l);
            }
        } else if let Some(rest) = msg.strip_prefix("ISLE simplify_skeleton ") {
            skeleton.extend(loc(rest));
        } else if let Some(rest) = msg.strip_prefix(" -> simplify_skeleton: yielded ") {
            let n = rest.split(' ').next().unwrap_or("?");
            println!("simplify_skeleton: {} -> {n}", skeleton.join(" "));
            skeleton.clear();
        } else if let Some(rest) = msg.strip_prefix("  -> returned from ISLE: ") {
            if let Some((v, rules)) = stack.pop() {
                let results = rest.split_once(" -> ").map(|(_, r)| r).unwrap_or(rest);
                println!("simplify {v}: {} -> {results}", rules.join(" "));
            }
        }
    }
}

static TRACER: Tracer = Tracer;

fn main() -> Result<()> {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    let opt = args.first().is_some_and(|a| a == "--opt");
    if opt {
        args.remove(0);
        OPT.with_borrow_mut(|o| *o = Some(OptState::default()));
    }
    let path = args.first().context("usage: isle-trace-oracle [--opt] <file.clif>")?;
    let src = std::fs::read_to_string(path).with_context(|| format!("reading {path}"))?;
    log::set_logger(&TRACER).map_err(|e| anyhow!("{e}"))?;
    log::set_max_level(if opt { log::LevelFilter::Trace } else { log::LevelFilter::Debug });

    let mut flags = settings::builder();
    for (k, v) in [
        ("opt_level", if opt { "speed" } else { "none" }),
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
