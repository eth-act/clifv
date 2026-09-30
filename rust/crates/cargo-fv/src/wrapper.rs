//! `fv-rustc`: the RUSTC_WRAPPER `cargo fv` installs, and the linker rustc runs for
//! executables of workspace members.
//!
//! Wrapper mode (`fv-rustc <rustc> <args>`): an invocation that codegens a workspace member
//! for the target gets `--emit=llvm-ir` (cg_clif then dumps every function's CLIF into
//! `<out-dir>/<unit>.clif/`) and hashed symbol mangling (v0 names of monomorphised iterator
//! adapters exceed the 255-byte file-name limit of those dumps). Libraries: after rustc, every
//! `*.rcgu.o` member of the rlib goes through [`pipeline::process_object`] and is put back.
//! Executables and test harnesses: rustc links through `fv-rustc` itself (linker mode), which
//! processes the crate's `*.rcgu.o` objects before running `rust-lld`, then checks the linked
//! binary. Every other invocation (dependencies, build scripts, `--print`) runs rustc as is.
//!
//! rustc copies `<unit>.<cgu>.rcgu.ll` to `<unit>.ll` when there is exactly one codegen unit,
//! a file cg_clif never writes; that copy error (and only it) makes fv-rustc create the empty
//! file and run rustc again.
use crate::config::Config;
use crate::pipeline::{self, read_syms, DumpIndex, MARKER};
use crate::report::{BinaryCheck, FnReport, Status, UnitReport};
use object::read::{Object, ObjectSymbol};
use std::collections::{HashMap, HashSet};
use std::ffi::OsString;
use std::fs;
use std::io::Write;
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

/// What the linker mode needs to know about the unit (passed through rustc's environment).
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
struct UnitMeta {
    unit: String,
    crate_name: String,
    package: String,
    kind: String,
    src: String,
    clif_dir: PathBuf,
}

fn eprint_fv(msg: &str) {
    eprintln!("fv-rustc: {msg}");
}

/// The value of a rustc option given as `--opt V` or `--opt=V`.
fn opt_values(args: &[String], opt: &str) -> Vec<String> {
    let mut v = Vec::new();
    let mut i = 0;
    while i < args.len() {
        if args[i] == opt {
            if let Some(x) = args.get(i + 1) {
                v.push(x.clone());
            }
            i += 2;
            continue;
        }
        if let Some(x) = args[i].strip_prefix(&format!("{opt}=")) {
            v.push(x.to_string());
        }
        i += 1;
    }
    v
}

/// `-C key=value` / `-Ckey=value`.
fn codegen_opt(args: &[String], key: &str) -> Option<String> {
    let mut found = None;
    let mut i = 0;
    while i < args.len() {
        let kv = if args[i] == "-C" {
            i += 1;
            args.get(i).map(|s| s.as_str())
        } else {
            args[i].strip_prefix("-C")
        };
        if let Some((k, v)) = kv.and_then(|kv| kv.split_once('=')) {
            if k == key {
                found = Some(v.to_string());
            }
        }
        i += 1;
    }
    found
}

/// Remove `-C linker=…` / `-Clinker=…` (and `-C linker-flavor=…`).
fn strip_linker(args: &[String]) -> Vec<String> {
    let mut out = Vec::new();
    let mut i = 0;
    let is_linker = |kv: &str| kv.starts_with("linker=") || kv.starts_with("linker-flavor=");
    while i < args.len() {
        if args[i] == "-C" && args.get(i + 1).is_some_and(|kv| is_linker(kv)) {
            i += 2;
            continue;
        }
        if args[i].strip_prefix("-C").is_some_and(is_linker) {
            i += 1;
            continue;
        }
        out.push(args[i].clone());
        i += 1;
    }
    out
}

/// Parsed facts about a rustc invocation that codegens a member crate.
struct Invocation {
    unit: String,
    src: String,
    crate_name: String,
    out_dir: PathBuf,
    kind: String,
    links: bool,
}

fn member_invocation(cfg: &Config, args: &[String]) -> Option<Invocation> {
    let crate_name = opt_values(args, "--crate-name").pop()?;
    if crate_name == "build_script_build" || crate_name == "___" || args.iter().any(|a| a.starts_with("--print")) {
        return None;
    }
    if opt_values(args, "--target").pop().as_deref() != Some(crate::TARGET) {
        return None;
    }
    let emit: Vec<String> = opt_values(args, "--emit").iter().flat_map(|e| e.split(',').map(String::from)).collect();
    if !emit.iter().any(|e| e == "link" || e.starts_with("link=")) {
        return None;
    }
    let manifest = std::env::var_os("CARGO_MANIFEST_DIR")?;
    if !cfg.is_member(Path::new(&manifest)) {
        return None;
    }
    let types: Vec<String> =
        opt_values(args, "--crate-type").iter().flat_map(|t| t.split(',').map(String::from)).collect();
    let test = args.iter().any(|a| a == "--test");
    let (kind, links) = if test {
        ("test".to_string(), true)
    } else if types.is_empty() || types.iter().all(|t| t == "bin") {
        ("bin".to_string(), true)
    } else if types.iter().all(|t| t == "lib" || t == "rlib") {
        ("lib".to_string(), false)
    } else {
        // dylib/cdylib/staticlib/proc-macro: plain cg_clif
        return None;
    };
    let extra = codegen_opt(args, "extra-filename").unwrap_or_default();
    let out_dir = PathBuf::from(opt_values(args, "--out-dir").pop()?);
    let src = args.iter().find(|a| a.ends_with(".rs") && !a.starts_with('-')).cloned().unwrap_or_default();
    Some(Invocation { unit: format!("{crate_name}{extra}"), src, crate_name, out_dir, kind, links })
}

/// The `could not copy "SRC" to "DST"` sources of rustc's `.ll` copy errors, if those are the
/// only errors in `stderr` (rustc's JSON diagnostics).
fn ll_copy_errors(stderr: &str) -> Option<Vec<PathBuf>> {
    let mut srcs = Vec::new();
    for line in stderr.lines() {
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else {
            if line.contains("error") {
                return None;
            }
            continue;
        };
        if v.get("$message_type").and_then(|t| t.as_str()) != Some("diagnostic") {
            continue;
        }
        if v.get("level").and_then(|l| l.as_str()) != Some("error") {
            continue;
        }
        let msg = v.get("message").and_then(|m| m.as_str()).unwrap_or("");
        if msg.starts_with("aborting due to") {
            continue;
        }
        let src = msg.strip_prefix("could not copy \"").and_then(|r| r.split_once('"')).map(|(s, _)| s);
        match src {
            Some(s) if s.ends_with(".ll") => srcs.push(PathBuf::from(s)),
            _ => return None,
        }
    }
    (!srcs.is_empty()).then_some(srcs)
}

fn run_rustc(rustc: &OsString, args: &[String], env: &[(String, String)]) -> (i32, Vec<u8>) {
    let child = Command::new(rustc)
        .args(args)
        .envs(env.iter().map(|(a, b)| (a, b)))
        .stdin(Stdio::inherit())
        .stdout(Stdio::inherit())
        .stderr(Stdio::piped())
        .spawn();
    match child.and_then(|c| c.wait_with_output()) {
        Ok(o) => (o.status.code().unwrap_or(1), o.stderr),
        Err(e) => (1, format!("fv-rustc: cannot run {}: {e}\n", Path::new(rustc).display()).into_bytes()),
    }
}

fn write_report(cfg: &Config, r: &UnitReport) {
    let _ = fs::create_dir_all(&cfg.report_dir);
    let path = cfg.report_dir.join(format!("{}.json", r.unit));
    if let Err(e) = serde_json::to_string_pretty(r).map_err(|e| e.to_string()).and_then(|s| fs::write(&path, s).map_err(|e| e.to_string())) {
        eprint_fv(&format!("{}: {e}", path.display()));
    }
}

fn new_report(cfg: &Config, m: &UnitMeta, artifact: &Path) -> UnitReport {
    UnitReport {
        unit: m.unit.clone(),
        crate_name: m.crate_name.clone(),
        package: m.package.clone(),
        kind: m.kind.clone(),
        src: m.src.clone(),
        artifact: artifact.display().to_string(),
        mode: cfg.mode.name().into(),
        theorem: cfg.mode.theorem().map(String::from),
        cgu_errors: vec![],
        functions: vec![],
        binary: None,
    }
}

/// Process CGU objects in place, appending to the report.
fn process_objects(cfg: &Config, m: &UnitMeta, objs: &[PathBuf], r: &mut UnitReport) -> Vec<bool> {
    let mut changed = Vec::new();
    // cg_clif writes no CLIF dump dir when the unit has no functions (e.g. a macro-only
    // crate like cfg-if): no dumps to process, every text symbol keeps cg_clif's code.
    if !m.clif_dir.exists() {
        for o in objs {
            match read_syms(o) {
                Ok(syms) => {
                    for s in syms.text.keys() {
                        r.functions.push(FnReport {
                            symbol: s.clone(),
                            instance: s.clone(),
                            status: Status::Fallback,
                            reason: Some("no CLIF dump (cg_clif emitted none for this unit)".into()),
                        });
                    }
                }
                Err(e) => r.cgu_errors.push(format!("{}: {e}", o.display())),
            }
            changed.push(false);
        }
        return changed;
    }
    let index = match DumpIndex::load(&m.clif_dir) {
        Ok(i) => i,
        Err(e) => {
            r.cgu_errors.push(format!("CLIF dumps: {e}"));
            return vec![false; objs.len()];
        }
    };
    for o in objs {
        let name = o.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        let res = pipeline::process_object(cfg, &index, o, &format!("{}/{name}", m.unit));
        if let Some(e) = res.error {
            r.cgu_errors.push(format!("{name}: {e}"));
        }
        r.functions.extend(res.functions);
        changed.push(res.changed);
    }
    r.functions.sort_by(|a, b| a.instance.cmp(&b.instance).then(a.symbol.cmp(&b.symbol)));
    changed
}

fn process_rlib(cfg: &Config, m: &UnitMeta, rlib: &Path) -> UnitReport {
    let mut r = new_report(cfg, m, rlib);
    let tmp = cfg.tmp_dir.join(format!("rlib-{}", pipeline::tag_of(&m.unit)));
    let _ = fs::remove_dir_all(&tmp);
    let res = (|| -> Result<(), String> {
        fs::create_dir_all(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?;
        let list = Command::new(&cfg.ar).arg("t").arg(rlib).output().map_err(|e| format!("{}: {e}", cfg.ar.display()))?;
        if !list.status.success() {
            return Err(format!("llvm-ar t {}: {}", rlib.display(), String::from_utf8_lossy(&list.stderr).trim()));
        }
        let members: Vec<String> = String::from_utf8_lossy(&list.stdout)
            .lines()
            .filter(|l| l.ends_with(".rcgu.o"))
            .map(String::from)
            .collect();
        if members.is_empty() {
            return Ok(());
        }
        let st = Command::new(&cfg.ar)
            .arg("x")
            .arg(format!("--output={}", tmp.display()))
            .arg(rlib)
            .args(&members)
            .status()
            .map_err(|e| e.to_string())?;
        if !st.success() {
            return Err(format!("llvm-ar x {} failed", rlib.display()));
        }
        let objs: Vec<PathBuf> = members.iter().map(|n| tmp.join(n)).collect();
        let changed = process_objects(cfg, m, &objs, &mut r);
        let upd: Vec<&PathBuf> = objs.iter().zip(changed).filter(|(_, c)| *c).map(|(o, _)| o).collect();
        if !upd.is_empty() {
            let st = Command::new(&cfg.ar).arg("r").arg(rlib).args(&upd).status().map_err(|e| e.to_string())?;
            if !st.success() {
                return Err(format!("llvm-ar r {} failed", rlib.display()));
            }
        }
        Ok(())
    })();
    if let Err(e) = res {
        r.cgu_errors.push(e);
    }
    if !cfg.keep_temps {
        let _ = fs::remove_dir_all(&tmp);
    }
    r
}

/// Wrapper mode. `args[0]` is the rustc cargo would have run.
pub fn wrapper_main(argv: Vec<OsString>) -> i32 {
    let Some((rustc, rest)) = argv.split_first() else {
        eprint_fv("usage: fv-rustc <rustc> <args>… (set as RUSTC_WRAPPER by `cargo fv`)");
        return 2;
    };
    let plain = || -> i32 {
        let e = Command::new(rustc).args(rest).exec();
        eprint_fv(&format!("cannot run {}: {e}", Path::new(rustc).display()));
        1
    };
    let cfg = match Config::from_env() {
        None => return plain(),
        Some(Err(e)) => {
            eprint_fv(&e);
            return 2;
        }
        Some(Ok(c)) => c,
    };
    let args: Vec<String> = rest.iter().map(|a| a.to_string_lossy().into_owned()).collect();
    let Some(inv) = member_invocation(&cfg, &args) else { return plain() };

    let clif_dir = inv.out_dir.join(format!("{}.clif", inv.unit));
    let meta = UnitMeta {
        unit: inv.unit.clone(),
        crate_name: inv.crate_name.clone(),
        package: std::env::var("CARGO_PKG_NAME").unwrap_or_default(),
        kind: inv.kind.clone(),
        src: inv.src.clone(),
        clif_dir: clif_dir.clone(),
    };
    let mut rargs = if inv.links { strip_linker(&args) } else { args.clone() };
    rargs.extend(["--emit=llvm-ir", "-Zunstable-options", "-Csymbol-mangling-version=hashed"].map(String::from));
    let mut env: Vec<(String, String)> = Vec::new();
    if inv.links {
        let me = std::env::current_exe().map(|p| p.display().to_string()).unwrap_or_else(|_| "fv-rustc".into());
        rargs.push(format!("-Clinker={me}"));
        rargs.push("-Clinker-flavor=ld.lld".into());
        env.push(("FV_LINK_META".into(), serde_json::to_string(&meta).expect("meta serialises")));
    }

    let _ = fs::remove_dir_all(&clif_dir);
    let (mut code, mut stderr) = run_rustc(rustc, &rargs, &env);
    if code != 0 {
        if let Some(srcs) = ll_copy_errors(&String::from_utf8_lossy(&stderr)) {
            for s in srcs {
                let _ = fs::write(&s, b"");
            }
            let _ = fs::remove_dir_all(&clif_dir);
            (code, stderr) = run_rustc(rustc, &rargs, &env);
        }
    }
    let _ = std::io::stderr().write_all(&stderr);
    if code != 0 {
        return code;
    }
    if !inv.links {
        let rlib = inv.out_dir.join(format!("lib{}.rlib", inv.unit));
        let r = if rlib.exists() {
            process_rlib(&cfg, &meta, &rlib)
        } else {
            let mut r = new_report(&cfg, &meta, &rlib);
            r.cgu_errors.push(format!("{} not found", rlib.display()));
            r
        };
        write_report(&cfg, &r);
    }
    code
}

/// Arguments of a rustc linker invocation, `@file` response files expanded (rustc writes one
/// argument per line, `\` escaping `\`, `"` and spaces for GNU-style linkers).
fn expand_args(args: Vec<OsString>) -> Vec<String> {
    let mut out = Vec::new();
    for a in args {
        let s = a.to_string_lossy().into_owned();
        if let Some(p) = s.strip_prefix('@') {
            if let Ok(text) = fs::read_to_string(p) {
                for l in text.lines() {
                    let mut u = String::new();
                    let mut esc = false;
                    for c in l.chars() {
                        if esc {
                            u.push(c);
                            esc = false;
                        } else if c == '\\' {
                            esc = true;
                        } else {
                            u.push(c);
                        }
                    }
                    out.push(u);
                }
                continue;
            }
        }
        out.push(s);
    }
    out
}

/// Check a linked executable: each marker's function symbol has the marker's address.
fn check_binary(path: &Path) -> BinaryCheck {
    let mut b = BinaryCheck { path: path.display().to_string(), ..Default::default() };
    let data = match fs::read(path) {
        Ok(d) => d,
        Err(e) => {
            b.note = Some(format!("unreadable: {e}"));
            return b;
        }
    };
    let file = match object::File::parse(&*data) {
        Ok(f) => f,
        Err(e) => {
            b.note = Some(format!("not an object file: {e}"));
            return b;
        }
    };
    let mut addrs: HashMap<&str, HashSet<u64>> = HashMap::new();
    let mut markers: Vec<(&str, u64)> = Vec::new();
    let mut any = false;
    for s in file.symbols() {
        any = true;
        let Ok(n) = s.name() else { continue };
        if s.is_undefined() {
            continue;
        }
        if let Some(f) = n.strip_prefix(MARKER) {
            markers.push((f, s.address()));
        } else {
            addrs.entry(n).or_default().insert(s.address());
        }
    }
    if !any {
        b.note = Some("no symbol table (stripped): not checked".into());
        return b;
    }
    for (f, a) in markers {
        match addrs.get(f) {
            Some(set) if set.contains(&a) => b.lean_functions_linked += 1,
            Some(_) => b.mismatches.push(format!("`{f}` resolves to other code than the Lean-compiled one")),
            None => b.mismatches.push(format!("`{f}` is missing next to its Lean marker")),
        }
    }
    b
}

/// Linker mode: rustc runs `fv-rustc` as the linker of a member's executable.
pub fn linker_main(meta_json: &str, argv: Vec<OsString>) -> i32 {
    let cfg = match Config::from_env() {
        Some(Ok(c)) => c,
        Some(Err(e)) => {
            eprint_fv(&e);
            return 2;
        }
        None => {
            eprint_fv("linker mode without FV_ROOT");
            return 2;
        }
    };
    let meta: UnitMeta = match serde_json::from_str(meta_json) {
        Ok(m) => m,
        Err(e) => {
            eprint_fv(&format!("FV_LINK_META: {e}"));
            return 2;
        }
    };
    let args = expand_args(argv.clone());
    let output = args.iter().position(|a| a == "-o").and_then(|i| args.get(i + 1)).map(PathBuf::from).unwrap_or_default();
    let prefix = format!("{}.", meta.unit);
    let objs: Vec<PathBuf> = args
        .iter()
        .filter(|a| a.ends_with(".rcgu.o"))
        .map(PathBuf::from)
        .filter(|p| p.file_name().is_some_and(|n| n.to_string_lossy().starts_with(&prefix)))
        .collect();
    let mut r = new_report(&cfg, &meta, &output);
    process_objects(&cfg, &meta, &objs, &mut r);
    write_report(&cfg, &r);
    let status = Command::new(&cfg.rust_lld).args(&argv).status();
    let code = match status {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => {
            eprint_fv(&format!("cannot run {}: {e}", cfg.rust_lld.display()));
            return 1;
        }
    };
    if code == 0 {
        r.binary = Some(check_binary(&output));
        write_report(&cfg, &r);
    }
    code
}
