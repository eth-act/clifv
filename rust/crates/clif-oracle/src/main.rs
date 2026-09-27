//! `clif-oracle`: the Cranelift side of the M0 cross-check.
//!
//! * `clif-oracle interp <file.clif>` parses the file with `cranelift-reader` and runs every
//!   `; run:`/`; print:` command on `cranelift-interpreter`, exactly as
//!   `cranelift/filetests/src/test_interpret.rs` does (one `FunctionStore` with all functions
//!   of the file, fresh interpreter state per command, the same libcall handler). It prints
//!   one JSON record per command (JSON lines); the schema is in `docs/contracts/clif.md`.
//! * `clif-oracle check <file.clif>` parses the file and runs the Cranelift verifier on every
//!   function. Exit status 0 iff the file parses and every function verifies.

use std::panic::{AssertUnwindSafe, catch_unwind};
use std::process::ExitCode;

use anyhow::{Context, Result, bail};
use cranelift_codegen::data_value::DataValue;
use cranelift_codegen::ir::{Function, LibCall};
use cranelift_codegen::settings;
use cranelift_interpreter::environment::FunctionStore;
use cranelift_interpreter::interpreter::{Interpreter, InterpreterState, LibCallValues};
use cranelift_interpreter::step::{ControlFlow, CraneliftTrap};
use cranelift_reader::{Comparison, Details, ParseOptions, RunCommand, parse_run_command};
use serde_json::{Value, json};

/// Instruction budget per run command (the interpreter's `fuel`).

/// Stack size of the interpreter thread.
const STACK_BYTES: usize = 1 << 30;
const FUEL: u64 = 100_000_000;

/// `{"ty": "i32", "bits": "0x0000002a"}`: the value's bytes as a little-endian unsigned
/// number, zero-padded to the type's width.
fn value_json(v: &DataValue) -> Value {
    let ty = v.ty();
    let n = ty.bytes() as usize;
    let mut buf = vec![0u8; n];
    v.write_to_slice_le(&mut buf);
    let hex: String = buf.iter().rev().map(|b| format!("{b:02x}")).collect();
    json!({ "ty": ty.to_string(), "bits": format!("0x{hex}") })
}

fn values_json(vs: &[DataValue]) -> Value {
    Value::Array(vs.iter().map(value_json).collect())
}

fn trap_name(t: &CraneliftTrap) -> String {
    match t {
        CraneliftTrap::User(code) => code.to_string(),
        CraneliftTrap::BadSignature => "bad_signature".to_string(),
        CraneliftTrap::UnreachableCodeReached => "unreachable".to_string(),
        CraneliftTrap::HeapMisaligned => "heap_misaligned".to_string(),
        CraneliftTrap::Debug => "debug".to_string(),
    }
}

/// Run one invocation on a fresh interpreter, as `test_interpret.rs` does.
fn invoke(store: &FunctionStore, name: &str, args: &[DataValue]) -> Value {
    let state = InterpreterState::default()
        .with_function_store(store.clone())
        .with_libcall_handler(|libcall: LibCall, args: LibCallValues| {
            use LibCall::*;
            Ok(smallvec::smallvec![match (libcall, &args[..]) {
                (CeilF32, [DataValue::F32(a)]) => DataValue::F32(a.ceil()),
                (CeilF64, [DataValue::F64(a)]) => DataValue::F64(a.ceil()),
                (FloorF32, [DataValue::F32(a)]) => DataValue::F32(a.floor()),
                (FloorF64, [DataValue::F64(a)]) => DataValue::F64(a.floor()),
                (TruncF32, [DataValue::F32(a)]) => DataValue::F32(a.trunc()),
                (TruncF64, [DataValue::F64(a)]) => DataValue::F64(a.trunc()),
                _ => return Err(CraneliftTrap::UnreachableCodeReached),
            }])
        });
    let func_name = format!("%{name}");
    let result = catch_unwind(AssertUnwindSafe(|| {
        Interpreter::new(state)
            .with_fuel(Some(FUEL))
            .call_by_name(&func_name, args)
            .map(|cf| match cf {
                ControlFlow::Return(vals) => json!({ "returned": values_json(&vals) }),
                ControlFlow::Trap(t) => json!({ "trapped": trap_name(&t) }),
                other => json!({ "error": format!("unexpected control flow: {other:?}") }),
            })
    }));
    match result {
        Ok(Ok(v)) => v,
        Ok(Err(e)) => json!({ "error": e.to_string() }),
        Err(p) => {
            let msg = p
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "panic".to_string());
            json!({ "error": format!("interpreter panicked: {msg}") })
        }
    }
}

/// Function name without the leading `%` (testcase names) or its display form.
fn plain_name(f: &Function) -> String {
    let s = f.name.to_string();
    s.strip_prefix('%').map(str::to_string).unwrap_or(s)
}

fn interp_function(store: &FunctionStore, func: &Function, details: &Details) -> Vec<Value> {
    let attached = plain_name(func);
    let mut out = Vec::new();
    for comment in &details.comments {
        let cmd = match parse_run_command(comment.text, &func.signature) {
            Ok(Some(cmd)) => cmd,
            Ok(None) => continue,
            Err(e) => {
                out.push(json!({
                    "attached": attached, "func": attached, "args": [],
                    "expected": Value::Null,
                    "actual": { "error": format!("run command does not parse: {e}") },
                }));
                continue;
            }
        };
        let (inv, expected) = match &cmd {
            RunCommand::Print(inv) => (inv, Value::Null),
            RunCommand::Run(inv, cmp, vals) => {
                let cmp = match cmp {
                    Comparison::Equals => "==",
                    Comparison::NotEquals => "!=",
                };
                (inv, json!({ "cmp": cmp, "values": values_json(vals) }))
            }
        };
        // A bare `; run` has the invocation name `default`: it means the attached function
        // (as in `test run`).
        let name = if inv.func == "default" { attached.clone() } else { inv.func.clone() };
        let actual = invoke(store, &name, &inv.args);
        out.push(json!({
            "attached": attached,
            "func": name,
            "args": values_json(&inv.args),
            "expected": expected,
            "actual": actual,
        }));
    }
    out
}

fn interp(path: &str) -> Result<bool> {
    let text = std::fs::read_to_string(path).with_context(|| format!("reading {path}"))?;
    let test = match cranelift_reader::parse_test(&text, ParseOptions::default()) {
        Ok(t) => t,
        Err(e) => {
            println!("{}", json!({ "file_error": e.to_string() }));
            return Ok(false);
        }
    };
    let mut store = FunctionStore::default();
    for (func, _) in &test.functions {
        store.add(func.name.to_string(), func);
    }
    for (func, details) in &test.functions {
        for rec in interp_function(&store, func, details) {
            println!("{rec}");
        }
    }
    Ok(true)
}

fn check(path: &str) -> Result<bool> {
    let text = std::fs::read_to_string(path).with_context(|| format!("reading {path}"))?;
    let test = match cranelift_reader::parse_test(&text, ParseOptions::default()) {
        Ok(t) => t,
        Err(e) => {
            println!("{path}: parse error: {e}");
            return Ok(false);
        }
    };
    let flags = settings::Flags::new(settings::builder());
    let mut ok = true;
    for (func, _) in &test.functions {
        if let Err(errors) = cranelift_codegen::verify_function(func, &flags) {
            ok = false;
            println!("{path}: {}: verifier errors:\n{errors}", func.name);
        }
    }
    if ok {
        println!("{path}: ok ({} functions)", test.functions.len());
    }
    Ok(ok)
}

fn run() -> Result<bool> {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match args.as_slice() {
        [cmd, path] if cmd == "interp" => interp(path),
        [cmd, path] if cmd == "check" => check(path),
        _ => bail!("usage: clif-oracle interp <file.clif> | clif-oracle check <file.clif>"),
    }
}

fn main() -> ExitCode {
    // Interpreter panics (unimplemented opcodes) are reported as JSON errors, not on stderr.
    std::panic::set_hook(Box::new(|_| {}));
    // The interpreter recurses on the host stack for CLIF calls (e.g. deep `return_call`
    // loops), so run it on a thread with a large stack.
    let worker = std::thread::Builder::new()
        .stack_size(STACK_BYTES)
        .spawn(run)
        .expect("spawning the interpreter thread");
    match worker.join().unwrap_or_else(|_| Err(anyhow::anyhow!("worker thread panicked"))) {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("clif-oracle: {e:#}");
            ExitCode::from(2)
        }
    }
}
