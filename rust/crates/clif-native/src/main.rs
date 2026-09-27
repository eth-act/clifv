//! `clif-native`: runs the `; run:`/`; print:` commands of a .clif file natively.
//!
//! usage: clif-native <file.clif> [--link <obj-or-archive>]... [--keep <dir>] [--timeout <secs>]
//!
//! Every function of the file is compiled for `aarch64-unknown-linux-gnu` with the
//! verification-friendly settings of `clif2obj` (same code path). For each function invoked by
//! a run command, a CLIF trampoline `__clifnative_tramp_N(i64 buf)` loads the arguments from
//! 16-byte slots of `buf`, calls the function (AAPCS64, or the function's own calling
//! convention) and stores every result back into the slots. A freestanding C harness
//! (`harness.c`, built with clang) runs the commands in order, catches traps with a signal
//! handler and reports raw results on stdout; the executable is linked statically with
//! `rust-lld` together with the `--link` objects and run under `qemu-aarch64-static`.
//!
//! Output: one JSON record per run command on stdout, in the clif-oracle schema
//! (`docs/contracts/clif.md`); traps map the faulting PC through Cranelift's trap table to
//! `{"trapped": "<code>"}`. Details and limitations: `docs/contracts/drivers.md`.

use std::collections::HashMap;
use std::io::Read;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, ExitStatus, Stdio};
use std::sync::mpsc::{self, RecvTimeoutError};
use std::time::Duration;

use anyhow::{Context as _, Result, anyhow, bail};
use clif2obj::{CompiledFunc, ObjectCompiler, Options};
use clif_runlines::{RunLine, run_lines, values_json};
use cranelift_codegen::data_value::DataValue;
use cranelift_codegen::ir::{
    AbiParam, ArgumentPurpose, ExtFuncData, ExternalName, Function, InstBuilder, MemFlagsData, Signature, Type,
    UserFuncName, types,
};
use cranelift_codegen::isa::{OwnedTargetIsa, TargetFrontendConfig};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use serde_json::{Value, json};

const TRIPLE: &str = "aarch64-unknown-linux-gnu";
/// Bytes per argument/result slot of the trampoline buffer (the widest type is 16 bytes).
const SLOT: usize = 16;
const HARNESS_C: &str = include_str!("harness.c");
const TRAMP_PREFIX: &str = "__clifnative_tramp_";
/// Guest stack size given to qemu (`-s`); deep CLIF recursion needs more than qemu's 8 MiB.
const STACK_BYTES: u64 = 1 << 30;

const USAGE: &str =
    "usage: clif-native <file.clif> [--link <obj-or-archive>]... [--keep <dir>] [--timeout <secs>]";

struct Tools {
    clang: String,
    lld: String,
    qemu: String,
}

impl Tools {
    /// `CLIF_NATIVE_CLANG` (default `clang`), `CLIF_NATIVE_LLD` (default: `rust-lld` of the
    /// active Rust toolchain), `CLIF_NATIVE_QEMU` (default `qemu-aarch64-static`).
    fn from_env() -> Tools {
        let lld = std::env::var("CLIF_NATIVE_LLD").unwrap_or_else(|_| toolchain_rust_lld().unwrap_or_else(|| "rust-lld".into()));
        Tools {
            clang: std::env::var("CLIF_NATIVE_CLANG").unwrap_or_else(|_| "clang".into()),
            lld,
            qemu: std::env::var("CLIF_NATIVE_QEMU").unwrap_or_else(|_| "qemu-aarch64-static".into()),
        }
    }
}

fn toolchain_rust_lld() -> Option<String> {
    let out = |args: &[&str]| -> Option<String> {
        let o = Command::new("rustc").args(args).output().ok()?;
        o.status.success().then(|| String::from_utf8_lossy(&o.stdout).into_owned())
    };
    let sysroot = out(&["--print", "sysroot"])?;
    let host = out(&["-vV"])?.lines().find_map(|l| l.strip_prefix("host: ").map(str::to_string))?;
    let p = Path::new(sysroot.trim()).join("lib/rustlib").join(host).join("bin/rust-lld");
    p.exists().then(|| p.display().to_string())
}

struct Config {
    file: String,
    links: Vec<PathBuf>,
    keep: Option<PathBuf>,
    timeout: Duration,
    tools: Tools,
}

fn parse_args() -> Result<Config> {
    let mut args = std::env::args().skip(1);
    let (mut file, mut links, mut keep, mut timeout) = (None, Vec::new(), None, Duration::from_secs(20));
    while let Some(a) = args.next() {
        let mut value = || args.next().ok_or_else(|| anyhow!("{a} needs a value\n{USAGE}"));
        match a.as_str() {
            "--link" => links.push(PathBuf::from(value()?)),
            "--keep" => keep = Some(PathBuf::from(value()?)),
            "--timeout" => timeout = Duration::from_secs_f64(value()?.parse().context("--timeout")?),
            s if s.starts_with("--") => bail!("unknown option {s}\n{USAGE}"),
            _ if file.is_none() => file = Some(a),
            _ => bail!("{USAGE}"),
        }
    }
    Ok(Config { file: file.ok_or_else(|| anyhow!("{USAGE}"))?, links, keep, timeout, tools: Tools::from_env() })
}

fn panic_message(p: Box<dyn std::any::Any + Send>) -> String {
    p.downcast_ref::<String>()
        .cloned()
        .or_else(|| p.downcast_ref::<&str>().map(|s| s.to_string()))
        .unwrap_or_else(|| "panic".into())
}

/// The file's functions and why some of them cannot be used.
struct Funcs<'a> {
    funcs: Vec<&'a Function>,
    names: Vec<String>,
    index: HashMap<String, usize>,
    callees: Vec<Vec<String>>,
    /// Functions excluded from the executable, with the reason.
    bad: HashMap<usize, Excluded>,
}

/// Why a function is not in the executable.
struct Excluded {
    /// Cranelift rejected the function or one of its callees (for aarch64 with the fixed
    /// settings): verifier error, unsupported lowering, or a Cranelift panic. Run commands
    /// then report `{"error": "not compiled: ..."}` (counted separately by `clif-results`).
    not_compiled: bool,
    why: String,
}

impl Excluded {
    fn not_compiled(why: String) -> Excluded {
        Excluded { not_compiled: true, why }
    }
    fn other(why: String) -> Excluded {
        Excluded { not_compiled: false, why }
    }
}

impl Funcs<'_> {
    /// Excludes every function that (transitively) calls an excluded function.
    fn propagate(&mut self) {
        loop {
            let mut changed = false;
            for i in 0..self.funcs.len() {
                if self.bad.contains_key(&i) {
                    continue;
                }
                let culprit = self.callees[i]
                    .iter()
                    .find(|c| self.index.get(c.as_str()).is_some_and(|j| self.bad.contains_key(j)));
                if let Some(c) = culprit {
                    let callee = &self.bad[&self.index[c.as_str()]];
                    let why = format!("calls %{c}: {}", callee.why);
                    self.bad.insert(i, Excluded { not_compiled: callee.not_compiled, why });
                    changed = true;
                }
            }
            if !changed {
                return;
            }
        }
    }
}

/// `__clifnative_tramp_<k>(i64 buf)`: loads the callee's arguments from `buf`, calls it and
/// stores its results into `buf` (slot `i` at byte `16 * i`).
fn trampoline(k: usize, callee: &str, sig: &Signature, target: TargetFrontendConfig) -> Function {
    let mut tsig = Signature::new(target.default_call_conv);
    tsig.params.push(AbiParam::new(types::I64));
    let mut func = Function::with_name_signature(UserFuncName::testcase(format!("{TRAMP_PREFIX}{k}")), tsig);
    let mut fctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut func, &mut fctx);
    let block = b.create_block();
    b.append_block_params_for_function_params(block);
    b.switch_to_block(block);
    b.seal_block(block);
    let buf = b.block_params(block)[0];
    let sigref = b.import_signature(sig.clone());
    let fref = b.import_function(ExtFuncData {
        name: ExternalName::testcase(callee),
        signature: sigref,
        colocated: false,
        patchable: false,
    });
    let flags = MemFlagsData::trusted();
    let args: Vec<_> = sig
        .params
        .iter()
        .enumerate()
        .map(|(i, p)| b.ins().load(p.value_type, flags, buf, (i * SLOT) as i32))
        .collect();
    let call = b.ins().call(fref, &args);
    let results = b.inst_results(call).to_vec();
    for (j, r) in results.into_iter().enumerate() {
        b.ins().store(flags, r, buf, (j * SLOT) as i32);
    }
    b.ins().return_(&[]);
    b.finalize(target);
    func
}

/// Why `line` cannot run (or `None` if it can).
fn line_error(line: &RunLine, funcs: &Funcs) -> Option<String> {
    let Some(&i) = funcs.index.get(&line.func) else {
        return Some(format!("no function %{} in the file", line.func));
    };
    if let Some(ex) = funcs.bad.get(&i) {
        return Some(if ex.not_compiled {
            format!("not compiled: %{}: {}", line.func, ex.why)
        } else {
            format!("%{} is not available: {}", line.func, ex.why)
        });
    }
    let sig = &funcs.funcs[i].signature;
    // A `vmctx` parameter is an ordinary pointer argument at the ABI level; the run command
    // supplies its value (as in Cranelift's `test run`).
    let plain = |p: &&AbiParam| matches!(p.purpose, ArgumentPurpose::Normal | ArgumentPurpose::VMContext);
    if let Some(p) = sig.params.iter().chain(&sig.returns).find(|p| !plain(p)) {
        return Some(format!("%{}: parameter purpose {} is not supported", line.func, p.purpose));
    }
    if let Some(p) = sig.params.iter().chain(&sig.returns).find(|p| p.value_type.bytes() as usize > SLOT) {
        return Some(format!("%{}: type {} is wider than {SLOT} bytes", line.func, p.value_type));
    }
    let arg_tys: Vec<Type> = line.args.iter().map(|a| a.ty()).collect();
    let param_tys: Vec<Type> = sig.params.iter().map(|p| p.value_type).collect();
    // The reader types vector literals by size only (`i8x16`/`i8x8`), like `DataValue`.
    let fits = |a: &Type, p: &Type| a == p || (a.is_vector() && p.is_vector() && a.bytes() == p.bytes());
    if arg_tys.len() != param_tys.len() || !arg_tys.iter().zip(&param_tys).all(|(a, p)| fits(a, p)) {
        return Some(format!(
            "argument types {arg_tys:?} do not match the parameters {param_tys:?} of %{}",
            line.func
        ));
    }
    None
}

/// One runnable command in the executable.
struct Run {
    line: usize,
    tramp: usize,
    args: Vec<u8>,
    ret_types: Vec<Type>,
}

/// A linked test executable.
struct Exe {
    path: PathBuf,
    runs: Vec<Run>,
    /// Functions in the order of the harness' `clifnative_fns` table: name and trap table.
    fns: Vec<(String, HashMap<u32, String>)>,
}

fn c_string(s: &str) -> String {
    s.chars().flat_map(|c| if c == '"' || c == '\\' { vec!['\\', c] } else { vec![c] }).collect()
}

fn tables_h(runs: &[Run], compiled: &[CompiledFunc], tramp_names: &[String]) -> String {
    use std::fmt::Write as _;
    let slots = runs.iter().map(|r| (r.args.len() / SLOT).max(r.ret_types.len())).max().unwrap_or(1).max(1);
    let mut h = String::new();
    writeln!(h, "#define CLIFNATIVE_BUF_SIZE {}", slots * SLOT).unwrap();
    writeln!(h, "#define CLIFNATIVE_NRUNS {}", runs.len()).unwrap();
    writeln!(h, "#define CLIFNATIVE_NFNS {}", compiled.len()).unwrap();
    for (k, name) in tramp_names.iter().enumerate() {
        writeln!(h, "extern void clifnative_tramp_{k}(void *) __asm__(\"{}\");", c_string(name)).unwrap();
    }
    for (k, f) in compiled.iter().enumerate() {
        writeln!(h, "extern const u8 clifnative_fn_{k}[] __asm__(\"{}\");", c_string(&f.name)).unwrap();
    }
    for (k, r) in runs.iter().enumerate() {
        let bytes: Vec<String> = r.args.iter().map(|b| b.to_string()).collect();
        let body = if bytes.is_empty() { "0".to_string() } else { bytes.join(",") };
        writeln!(h, "static const u8 clifnative_args_{k}[] = {{{body}}};").unwrap();
    }
    writeln!(h, "static const struct clifnative_run clifnative_runs[] = {{").unwrap();
    for (k, r) in runs.iter().enumerate() {
        writeln!(
            h,
            "  {{clifnative_tramp_{}, clifnative_args_{k}, {}, {}}},",
            r.tramp,
            r.args.len(),
            r.ret_types.len() * SLOT
        )
        .unwrap();
    }
    writeln!(h, "}};\nstatic const struct clifnative_fn clifnative_fns[] = {{").unwrap();
    for (k, f) in compiled.iter().enumerate() {
        writeln!(h, "  {{clifnative_fn_{k}, {}}},", f.code.len()).unwrap();
    }
    writeln!(h, "}};").unwrap();
    h
}

fn run_tool(cmd: &mut Command, what: &str) -> Result<std::process::Output> {
    cmd.output().with_context(|| format!("running {what} ({cmd:?})"))
}

/// Outcome of trying to build the executable.
enum Build {
    Linked(Exe),
    /// The link failed because these symbols are undefined.
    Undefined(Vec<String>, Vec<CompiledFunc>),
    /// A function that passed the stand-alone compile check failed inside the object.
    FuncFailed(usize, String),
}

fn build(
    cfg: &Config,
    isa: &OwnedTargetIsa,
    funcs: &Funcs,
    lines: &[RunLine],
    runnable: &[usize],
    dir: &Path,
) -> Result<Build> {
    // Trampolines, one per invoked function.
    let mut tramp_of: HashMap<usize, usize> = HashMap::new();
    let mut tramps: Vec<Function> = Vec::new();
    let mut runs = Vec::new();
    for &li in runnable {
        let line = &lines[li];
        let fi = funcs.index[&line.func];
        let tramp = *tramp_of.entry(fi).or_insert_with(|| {
            let sig = &funcs.funcs[fi].signature;
            tramps.push(trampoline(tramps.len(), &funcs.names[fi], sig, isa.frontend_config()));
            tramps.len() - 1
        });
        let mut args = vec![0u8; line.args.len() * SLOT];
        for (i, a) in line.args.iter().enumerate() {
            a.write_to_slice_le(&mut args[i * SLOT..]);
        }
        let ret_types = funcs.funcs[fi].signature.returns.iter().map(|p| p.value_type).collect();
        runs.push(Run { line: li, tramp, args, ret_types });
    }

    let good: Vec<usize> = (0..funcs.funcs.len()).filter(|i| !funcs.bad.contains_key(i)).collect();
    let mut oc = ObjectCompiler::new(isa.clone(), Options::default())?;
    let mut decl: Vec<&Function> = good.iter().map(|&i| funcs.funcs[i]).collect();
    decl.extend(tramps.iter());
    oc.declare(&decl)?;
    let mut compiled = Vec::new();
    for &i in &good {
        match catch_unwind(AssertUnwindSafe(|| oc.define(funcs.funcs[i]))) {
            Ok(Ok(c)) => compiled.push(c),
            Ok(Err(e)) => return Ok(Build::FuncFailed(i, format!("{e:#}"))),
            Err(p) => return Ok(Build::FuncFailed(i, format!("Cranelift panicked: {}", panic_message(p)))),
        }
    }
    let mut tramp_names = Vec::new();
    for t in &tramps {
        let c = oc.define(t).context("compiling a trampoline")?;
        tramp_names.push(c.name.clone());
        compiled.push(c);
    }
    let obj = dir.join("clif.o");
    std::fs::write(&obj, oc.finish()?)?;

    std::fs::write(dir.join("harness.c"), HARNESS_C)?;
    std::fs::write(dir.join("clifnative_tables.h"), tables_h(&runs, &compiled, &tramp_names))?;
    let harness_o = dir.join("harness.o");
    let out = run_tool(
        Command::new(&cfg.tools.clang)
            .args([
                "--target=aarch64-linux-gnu",
                "-ffreestanding",
                "-fno-builtin",
                "-nostdlib",
                "-fno-pic",
                "-fno-stack-protector",
                "-mgeneral-regs-only",
                "-O2",
                "-Wall",
                "-Werror",
                "-c",
            ])
            .arg(dir.join("harness.c"))
            .arg("-o")
            .arg(&harness_o),
        "clang",
    )?;
    if !out.status.success() {
        bail!("compiling the harness failed:\n{}", String::from_utf8_lossy(&out.stderr));
    }

    let exe = dir.join("test.exe");
    let out = run_tool(
        Command::new(&cfg.tools.lld)
            .args(["-flavor", "gnu", "-static", "--no-demangle", "-e", "_start", "-o"])
            .arg(&exe)
            .arg(&harness_o)
            .arg(&obj)
            .args(&cfg.links),
        "rust-lld",
    )?;
    if !out.status.success() {
        let err = String::from_utf8_lossy(&out.stderr);
        let undefined: Vec<String> = err
            .lines()
            .filter_map(|l| l.split_once("undefined symbol: ").map(|(_, s)| s.trim().to_string()))
            .collect();
        if undefined.is_empty() {
            bail!("linking failed:\n{err}");
        }
        return Ok(Build::Undefined(undefined, compiled));
    }
    let fns = compiled
        .iter()
        .map(|c| (c.name.clone(), c.traps.iter().map(|t| (t.offset, t.code.clone())).collect()))
        .collect();
    Ok(Build::Linked(Exe { path: exe, runs, fns }))
}

fn signal_name(signo: u32) -> String {
    match signo {
        4 => "SIGILL".into(),
        5 => "SIGTRAP".into(),
        7 => "SIGBUS".into(),
        8 => "SIGFPE".into(),
        11 => "SIGSEGV".into(),
        n => format!("signal {n}"),
    }
}

/// One process run of the executable from run `start`: stdout, and how it ended.
fn spawn_once(cfg: &Config, exe: &Path, start: usize) -> Result<(Vec<u8>, Result<ExitStatus, String>, String)> {
    let mut child = Command::new(&cfg.tools.qemu)
        .arg("-s")
        .arg(STACK_BYTES.to_string())
        .arg(exe)
        .arg(start.to_string())
        .stdin(Stdio::null())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .with_context(|| format!("running {}", cfg.tools.qemu))?;
    let mut stdout = child.stdout.take().expect("piped stdout");
    let mut stderr = child.stderr.take().expect("piped stderr");
    let (tx, rx) = mpsc::channel::<Vec<u8>>();
    let reader = std::thread::spawn(move || {
        let mut chunk = vec![0u8; 1 << 16];
        while let Ok(n) = stdout.read(&mut chunk) {
            if n == 0 || tx.send(chunk[..n].to_vec()).is_err() {
                break;
            }
        }
    });
    let err_reader = std::thread::spawn(move || {
        let mut s = String::new();
        let _ = stderr.read_to_string(&mut s);
        s
    });
    let mut bytes = Vec::new();
    let mut timed_out = false;
    loop {
        match rx.recv_timeout(cfg.timeout) {
            Ok(c) => bytes.extend(c),
            Err(RecvTimeoutError::Disconnected) => break,
            Err(RecvTimeoutError::Timeout) => {
                timed_out = true;
                let _ = child.kill();
                while let Ok(c) = rx.recv() {
                    bytes.extend(c);
                }
                break;
            }
        }
    }
    let status = child.wait()?;
    let _ = reader.join();
    let stderr = err_reader.join().unwrap_or_default();
    let end = if timed_out {
        Err(format!("timed out (no result for {:?})", cfg.timeout))
    } else {
        Ok(status)
    };
    Ok((bytes, end, stderr))
}

fn u32_at(b: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(b[at..at + 4].try_into().unwrap())
}

/// Runs every command of `exe`; one `actual` outcome per run.
fn execute(cfg: &Config, exe: &Exe) -> Result<Vec<Value>> {
    let n = exe.runs.len();
    let mut out = Vec::with_capacity(n);
    while out.len() < n {
        let start = out.len();
        let (bytes, end, stderr) = spawn_once(cfg, &exe.path, start)?;
        let mut pos = 0;
        while out.len() < n && bytes.len() >= pos + 8 {
            let run = &exe.runs[out.len()];
            let (index, kind) = (u32_at(&bytes, pos) as usize, u32_at(&bytes, pos + 4));
            if index != out.len() {
                bail!("corrupt harness output: record for run {index}, expected {}", out.len());
            }
            match kind {
                0 => {
                    let len = run.ret_types.len() * SLOT;
                    if bytes.len() < pos + 8 + len {
                        break;
                    }
                    let res = &bytes[pos + 8..pos + 8 + len];
                    let vals: Vec<DataValue> = run
                        .ret_types
                        .iter()
                        .enumerate()
                        .map(|(j, ty)| DataValue::read_from_slice_le(&res[j * SLOT..], *ty))
                        .collect();
                    out.push(json!({ "returned": values_json(&vals) }));
                    pos += 8 + len;
                }
                1 => {
                    if bytes.len() < pos + 24 {
                        break;
                    }
                    let (signo, fi) = (u32_at(&bytes, pos + 8), u32_at(&bytes, pos + 12));
                    let offset = u64::from_le_bytes(bytes[pos + 16..pos + 24].try_into().unwrap());
                    let sig = signal_name(signo);
                    out.push(match exe.fns.get(fi as usize) {
                        Some((name, traps)) => {
                            match u32::try_from(offset).ok().and_then(|o| traps.get(&o)) {
                                Some(code) if matches!(signo, 4 | 7 | 8 | 11) => json!({ "trapped": code }),
                                _ => json!({ "error": format!("{sig} at %{name}+{offset:#x}, which is not a trap site") }),
                            }
                        }
                        None => json!({ "error": format!("{sig} at pc {offset:#x}, outside the compiled code") }),
                    });
                    pos += 24;
                }
                k => bail!("corrupt harness output: record kind {k}"),
            }
        }
        if out.len() < n {
            // The process ended (or hung) during run `out.len()`: report it, go on after it.
            let how = match end {
                Ok(s) => format!("the test process ended with {s}"),
                Err(t) => format!("the test process {t}"),
            };
            let detail = stderr.trim();
            let msg = if detail.is_empty() { how } else { format!("{how}: {detail}") };
            out.push(json!({ "error": msg }));
        }
    }
    Ok(out)
}

fn native(cfg: &Config, dir: &Path) -> Result<bool> {
    let text = std::fs::read_to_string(&cfg.file).with_context(|| format!("reading {}", cfg.file))?;
    let isa = clif2obj::isa(TRIPLE)?;
    let test = match clif2obj::parse_file(&text, &*isa) {
        Ok(t) => t,
        Err(e) => {
            println!("{}", json!({ "file_error": format!("{e:#}") }));
            return Ok(false);
        }
    };

    let funcs_v: Vec<&Function> = test.functions.iter().map(|(f, _)| f).collect();
    let mut funcs = Funcs {
        names: Vec::new(),
        index: HashMap::new(),
        callees: Vec::new(),
        bad: HashMap::new(),
        funcs: funcs_v,
    };
    for (i, f) in funcs.funcs.iter().enumerate() {
        let name = match clif2obj::symbol_name(&f.name) {
            Ok(n) => n,
            Err(e) => {
                funcs.bad.insert(i, Excluded::other(format!("{e:#}")));
                f.name.to_string()
            }
        };
        if funcs.index.insert(name.clone(), i).is_some() {
            bail!("function %{name} is defined twice");
        }
        funcs.names.push(name);
        match clif2obj::callees(f) {
            Ok(c) => funcs.callees.push(c),
            Err(e) => {
                funcs.callees.push(Vec::new());
                funcs.bad.entry(i).or_insert_with(|| Excluded::other(format!("{e:#}")));
            }
        }
    }
    // Stand-alone compile check, so that one function Cranelift rejects does not take the
    // whole file down.
    for (i, f) in funcs.funcs.iter().enumerate() {
        if funcs.bad.contains_key(&i) {
            continue;
        }
        let r = catch_unwind(AssertUnwindSafe(|| clif2obj::check_compiles(&*isa, f)));
        let why = match r {
            Ok(Ok(())) => continue,
            Ok(Err(e)) => format!("{e:#}"),
            Err(p) => format!("Cranelift panicked: {}", panic_message(p)),
        };
        funcs.bad.insert(i, Excluded::not_compiled(why));
    }
    funcs.propagate();

    let lines: Vec<RunLine> = test.functions.iter().flat_map(|(f, d)| run_lines(f, d)).collect();
    let mut actual: Vec<Option<Value>> = vec![None; lines.len()];

    let exe = loop {
        let mut runnable = Vec::new();
        for (li, line) in lines.iter().enumerate() {
            actual[li] = if let Some(rec) = line.parse_error_record() {
                Some(rec["actual"].clone())
            } else if let Some(e) = line_error(line, &funcs) {
                Some(json!({ "error": e }))
            } else {
                runnable.push(li);
                None
            };
        }
        if runnable.is_empty() {
            break None;
        }
        match build(cfg, &isa, &funcs, &lines, &runnable, dir)? {
            Build::Linked(exe) => break Some(exe),
            Build::FuncFailed(i, why) => {
                funcs.bad.insert(i, Excluded::not_compiled(why));
            }
            Build::Undefined(syms, compiled) => {
                let mut blamed = false;
                for sym in &syms {
                    for c in &compiled {
                        if c.relocs.iter().any(|r| &r.target == sym)
                            && let Some(&i) = funcs.index.get(&c.name)
                        {
                            funcs.bad.entry(i).or_insert_with(|| {
                                Excluded::other(format!(
                                    "unresolved external symbol `{sym}` (not defined in {} and not provided by --link)",
                                    cfg.file
                                ))
                            });
                            blamed = true;
                        }
                    }
                }
                if !blamed {
                    bail!("linking failed: undefined symbols {syms:?} not referenced by any CLIF function");
                }
                for sym in &syms {
                    eprintln!("clif-native: {}: unresolved external symbol `{sym}`", cfg.file);
                }
            }
        }
        funcs.propagate();
    };

    if let Some(exe) = exe {
        for (run, outcome) in exe.runs.iter().zip(execute(cfg, &exe)?) {
            actual[run.line] = Some(outcome);
        }
    }
    for (line, act) in lines.iter().zip(actual) {
        println!("{}", line.record(act.expect("every run command has an outcome")));
    }
    Ok(true)
}

fn run() -> Result<bool> {
    let cfg = parse_args()?;
    match &cfg.keep {
        Some(dir) => {
            std::fs::create_dir_all(dir).with_context(|| format!("creating {}", dir.display()))?;
            native(&cfg, dir)
        }
        None => {
            let nanos = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map(|d| d.as_nanos()).unwrap_or(0);
            let dir = std::env::temp_dir().join(format!("clif-native-{}-{nanos}", std::process::id()));
            std::fs::create_dir_all(&dir).with_context(|| format!("creating {}", dir.display()))?;
            let r = native(&cfg, &dir);
            let _ = std::fs::remove_dir_all(&dir);
            r
        }
    }
}

fn main() -> ExitCode {
    std::panic::set_hook(Box::new(|_| {}));
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("clif-native: {e:#}");
            ExitCode::from(2)
        }
    }
}
