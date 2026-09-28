//! `clif2obj`: compile a .clif file (emitted from Lean) to a relocatable object with the
//! verification-friendly settings, and dump per-function machine code, VCode, relocations
//! and trap tables for the M3 validator. Schemas: `docs/contracts/drivers.md`.
//!
//! usage: clif2obj [--colocated-externs] [--opt-level none|speed|speed_and_size] <input.clif>
//!        <target-triple> <out.o> <dump-dir>
//!
//! `--opt-level` (default `none`, the project setting) exists only to measure Cranelift's
//! mid-end (`scripts/lean-backend-metrics.sh`).

use std::path::Path;
use std::process::ExitCode;

use anyhow::{Context as _, Result, bail};
use clif2obj::{ObjectCompiler, Options};

const USAGE: &str = "usage: clif2obj [--colocated-externs] [--opt-level none|speed|speed_and_size] <input.clif> <target-triple> <out.o> <dump-dir>";

fn run() -> Result<()> {
    let mut opts = Options::default();
    let mut pos = Vec::new();
    let mut opt_level = "none".to_string();
    let mut args = std::env::args().skip(1);
    while let Some(a) = args.next() {
        match a.as_str() {
            "--colocated-externs" => opts.colocated_externs = true,
            "--opt-level" => opt_level = args.next().context("--opt-level needs a value")?,
            s if s.starts_with("--") => bail!("unknown option {s}\n{USAGE}"),
            _ => pos.push(a),
        }
    }
    let [input, triple, out, dump_dir] = pos.as_slice() else {
        bail!("{USAGE}");
    };

    let isa = clif2obj::isa_with_opt_level(triple, &opt_level)?;
    let src = std::fs::read_to_string(input).with_context(|| format!("reading {input}"))?;
    let test = clif2obj::parse_file(&src, &*isa).with_context(|| format!("parsing {input}"))?;
    let funcs: Vec<_> = test.functions.iter().map(|(f, _)| f).collect();

    let dump_dir = Path::new(dump_dir);
    std::fs::create_dir_all(dump_dir).with_context(|| format!("creating {}", dump_dir.display()))?;
    let mut compiler = ObjectCompiler::new(isa, opts)?;
    compiler.declare(&funcs)?;
    for f in funcs {
        let compiled = compiler.define(f)?;
        compiled.write_dump(dump_dir)?;
    }
    std::fs::write(out, compiler.finish()?).with_context(|| format!("writing {out}"))?;
    Ok(())
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("clif2obj: {e:#}");
            ExitCode::FAILURE
        }
    }
}
