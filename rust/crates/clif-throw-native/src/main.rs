//! `clif-throw-native <file.clif>`: the native oracle of `Clif.runX` (S10b,
//! `docs/plans/unwinding.md`). Compiles every function of the file with Cranelift's JIT for the
//! host (as Cranelift's own `test run` does: `runner.rs`, copied from `cranelift-filetests`),
//! with `preserve_frame_pointers` (the throw hostcall walks the frame-pointer chain), runs every
//! `; run:`/`; print:` command natively and prints one JSON record per command, in
//! `clif-oracle interp`'s schema (`docs/contracts/clif.md`), so `clif-filetest --oracle-dir`
//! compares `Clif.runX` with it.
//!
//! Throws go through `__cranelift_throw(entry_fp, exit_fp, exit_pc, tag: i32, payload1,
//! payload2)` (the hostcall of Cranelift's runner): it searches the Cranelift frames between
//! the thrower and `entry_fp` for the first `try_call` handler whose tag is `tag` or `default`,
//! in each frame's exception-table order, and resumes there with the two payload words.
//! A throw that no frame catches panics; the record is then an `error`.

mod runner;

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::ExitCode;

use anyhow::{Context, Result};
use clif_runlines::{plain_name, run_lines, values_json};
use cranelift_codegen::settings::{self, Configurable};
use cranelift_reader::ParseOptions;
use serde_json::json;

fn native(path: &str) -> Result<bool> {
    let text = std::fs::read_to_string(path).with_context(|| format!("reading {path}"))?;
    let test = match cranelift_reader::parse_test(&text, ParseOptions::default()) {
        Ok(t) => t,
        Err(e) => {
            println!("{}", json!({ "file_error": e.to_string() }));
            return Ok(false);
        }
    };
    let mut b = settings::builder();
    b.set("preserve_frame_pointers", "true")?;
    b.set("enable_verifier", "true")?;
    let flags = settings::Flags::new(b);
    let mut compiler = runner::TestFileCompiler::with_host_isa(flags)?;
    compiler.add_testfile(&test)?;
    let compiled = compiler.compile()?;
    for (func, details) in &test.functions {
        for line in run_lines(func, details) {
            if let Some(rec) = line.parse_error_record() {
                println!("{rec}");
                continue;
            }
            let Some((target, _)) = test.functions.iter().find(|(f, _)| plain_name(f) == line.func)
            else {
                println!("{}", line.record(json!({ "error": format!("no function %{}", line.func) })));
                continue;
            };
            let tramp = compiled.get_trampoline(target).context("trampoline")?;
            let out = catch_unwind(AssertUnwindSafe(|| tramp.call(&compiled, &line.args)));
            let actual = match out {
                Ok(vals) => json!({ "returned": values_json(&vals) }),
                Err(p) => {
                    let msg = p
                        .downcast_ref::<String>()
                        .cloned()
                        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                        .unwrap_or_else(|| "panic".to_string());
                    json!({ "error": format!("native run panicked: {msg}") })
                }
            };
            println!("{}", line.record(actual));
        }
    }
    Ok(true)
}

fn main() -> ExitCode {
    std::panic::set_hook(Box::new(|_| {}));
    let args: Vec<String> = std::env::args().skip(1).collect();
    let r = match args.as_slice() {
        [path] => native(path),
        _ => Err(anyhow::anyhow!("usage: clif-throw-native <file.clif>")),
    };
    match r {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("clif-throw-native: {e:#}");
            ExitCode::from(2)
        }
    }
}
