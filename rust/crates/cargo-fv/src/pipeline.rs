//! Per codegen unit: recompile cg_clif's functions with the Lean backend and splice the
//! result into cg_clif's object, in place.
//!
//! For one CGU object `obj` (cg_clif's output) and the crate's CLIF dump directory:
//!
//! 1. The functions of this CGU are the dumps whose `; symbol` is a text symbol defined in
//!    `obj` (cg_clif numbers `u0:N` per CGU module, so a CGU is the unit of decoding).
//! 2. `clif-decode` (Lean, `Front.decodeFn`) decodes every dump of the CGU: each external
//!    name replaced by the symbol cg_clif's module declared for it (the dump's external-name
//!    table, written by the patched cg_clif of `scripts/build-cg-clif.sh`), one reader-clean
//!    CLIF file per function. `clif-data-export` writes the object's data objects (`; data:`,
//!    for `cargo fv link-proof`). No data is copied: our code references cg_clif's data objects
//!    themselves, so every data object keeps a single identity (addresses of statics, vtables,
//!    `Location`s are the ones cg_clif's code and every other crate see).
//! 3. `lean-backend` compiles each function in its own file, so a call to another function is
//!    a call of an extern (`E2E.backend_correct_final_cleanup` covers extern calls through its callee
//!    contract) and a function the backend rejects does not drag its callers along: calls
//!    to it reach cg_clif's code.
//! 4. Safety net: every symbol our object for a function references must be defined or
//!    referenced by `obj` itself (or be a runtime helper std provides); otherwise the function
//!    falls back.
//! 5. Symbol surgery (llvm-objcopy): local symbols of `obj` that our code defines or references
//!    are renamed to a unique name and made global (so the references bind across objects);
//!    cg_clif's definitions of the functions we compiled are weakened. Our objects are linked
//!    with `ld -r`, renamed the same way and given a local marker `__fvlean$<symbol>` per
//!    function. Then `ld -r --unique obj ours` merges the two: each symbol we define resolves to
//!    our (strong) definition, including the relocations inside cg_clif's code and data
//!    (calls, vtables); cg_clif's copy stays as dead code. The renamed symbols are made local
//!    again, so the object's interface to the rest of the program is unchanged.
//! 6. Check on the merged object: every compiled symbol has its marker's address; otherwise the
//!    CGU is left as cg_clif wrote it (all fallback).
//!
//! Any failure leaves the object untouched and reports the functions as fallback: the build
//! never fails because of us.
use crate::config::{Config, Mode};
use crate::report::{FnReport, MidvalReport, Status};
use object::read::{Object, ObjectSymbol};
use object::{SymbolKind, SymbolScope};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Symbols a Lean-compiled function may reference although cg_clif's object does not: the
/// runtime helpers the Lean backend's i128 legalisation calls (compiler_builtins) and the mem*
/// functions (musl libc), all linked into every Rust executable.
const RUNTIME_HELPERS: &[&str] =
    &["memcpy", "memmove", "memset", "memcmp", "bcmp", "__udivti3", "__divti3", "__umodti3", "__modti3"];

/// Prefix of the per-function marker symbol.
pub const MARKER: &str = "__fvlean$";

/// A function's dump in the crate's CLIF directory.
#[derive(Clone, Debug)]
pub struct Dump {
    /// File name without `.unopt.clif`.
    pub stem: String,
    pub instance: String,
    /// Cranelift's `opt_level` in the dump's header (`set opt_level=…`): cg_clif's setting for
    /// the function, `none` for rustc's `-Copt-level=0` and `speed_and_size` for every other
    /// level (`--release`, or a profile raising `opt-level`); empty when the header has none.
    pub opt_level: String,
}

/// `; symbol` → dump, over one crate's `<unit>.clif/` directory.
pub struct DumpIndex {
    pub dir: PathBuf,
    pub by_symbol: HashMap<String, Dump>,
}

impl DumpIndex {
    pub fn load(dir: &Path) -> Result<DumpIndex, String> {
        let mut by_symbol = HashMap::new();
        let rd = fs::read_dir(dir).map_err(|e| format!("{}: {e}", dir.display()))?;
        for e in rd.flatten() {
            let name = e.file_name().to_string_lossy().into_owned();
            let Some(stem) = name.strip_suffix(".unopt.clif") else { continue };
            let text = fs::read_to_string(e.path()).map_err(|e| format!("{name}: {e}"))?;
            let mut symbol = None;
            let mut instance = String::new();
            let mut opt_level = String::new();
            for l in text.lines() {
                if let Some(s) = l.strip_prefix("set opt_level=") {
                    opt_level = s.trim().to_string();
                } else if let Some(s) = l.strip_prefix("; symbol ") {
                    symbol.get_or_insert_with(|| s.trim().to_string());
                } else if let Some(s) = l.strip_prefix("; instance ") {
                    instance = pretty_instance(s);
                    break;
                }
            }
            if let Some(s) = symbol {
                if instance.is_empty() {
                    instance = s.clone();
                }
                by_symbol.insert(s, Dump { stem: stem.to_string(), instance, opt_level });
            }
        }
        Ok(DumpIndex { dir: dir.to_path_buf(), by_symbol })
    }
}

/// `Instance { def: Item(DefId(0:5 ~ hello[fe56]::msg)), args: [] }` → `hello::msg`
/// (shims keep their kind: `DropGlue hello::S`; generic arguments are appended).
fn pretty_instance(s: &str) -> String {
    let kind = s
        .split_once("def: ")
        .map(|(_, r)| r.split('(').next().unwrap_or("").to_string())
        .unwrap_or_default();
    let path = s
        .split_once("~ ")
        .map(|(_, r)| r.split(')').next().unwrap_or(r).to_string())
        .unwrap_or_else(|| s.to_string());
    // drop crate disambiguators `name[1a2b]`
    let mut p = String::new();
    let mut skip = false;
    for c in path.chars() {
        match c {
            '[' => skip = true,
            ']' => skip = false,
            _ if !skip => p.push(c),
            _ => {}
        }
    }
    let args = s
        .split_once("), args: [")
        .map(|(_, r)| r.strip_suffix(" }").unwrap_or(r).strip_suffix(']').unwrap_or(r))
        .unwrap_or("");
    let mut out = if kind == "Item" || kind.is_empty() { p } else { format!("{kind} {p}") };
    if !args.is_empty() {
        out.push_str("::<");
        out.push_str(args);
        out.push('>');
    }
    if out.len() > 240 {
        let mut cut = 240;
        while !out.is_char_boundary(cut) {
            cut -= 1;
        }
        out.truncate(cut);
        out.push('…');
    }
    out
}

/// FNV-1a, for short unique tags.
pub fn tag_of(s: &str) -> String {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    format!("{:012x}", h & 0xffff_ffff_ffff)
}

/// Symbols of an ELF object.
pub(crate) struct ObjSyms {
    /// Defined text symbols → global (or weak)?
    pub(crate) text: HashMap<String, bool>,
    /// Every defined symbol name (functions, data).
    pub(crate) defined: BTreeSet<String>,
    /// Local definitions per name (a name defined locally twice is ambiguous).
    pub(crate) local_count: HashMap<String, usize>,
    pub(crate) undefined: BTreeSet<String>,
    /// name → (section index, value) of defined symbols (first definition).
    pub(crate) at: HashMap<String, (usize, u64)>,
}

pub(crate) fn read_syms(path: &Path) -> Result<ObjSyms, String> {
    let data = fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let file = object::File::parse(&*data).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut s = ObjSyms {
        text: HashMap::new(),
        defined: BTreeSet::new(),
        local_count: HashMap::new(),
        undefined: BTreeSet::new(),
        at: HashMap::new(),
    };
    for sym in file.symbols() {
        let Ok(name) = sym.name() else { continue };
        if name.is_empty() || matches!(sym.kind(), SymbolKind::Section | SymbolKind::File) {
            continue;
        }
        if sym.is_undefined() {
            s.undefined.insert(name.to_string());
            continue;
        }
        let local = sym.scope() == SymbolScope::Compilation;
        if local {
            *s.local_count.entry(name.to_string()).or_default() += 1;
        }
        if sym.kind() == SymbolKind::Text {
            s.text.insert(name.to_string(), !local);
        }
        s.defined.insert(name.to_string());
        if let Some(si) = sym.section_index() {
            s.at.entry(name.to_string()).or_insert((si.0, sym.address()));
        }
    }
    // a name both undefined and defined (not possible in one ELF object, but be safe)
    for d in &s.defined {
        s.undefined.remove(d);
    }
    Ok(s)
}

pub(crate) fn run(cmd: &mut Command) -> Result<String, String> {
    let out = cmd.output().map_err(|e| format!("{:?}: {e}", cmd.get_program()))?;
    if out.status.success() {
        Ok(String::from_utf8_lossy(&out.stderr).into_owned())
    } else {
        let err = String::from_utf8_lossy(&out.stderr);
        // the first `error` line (linkers), else the last line (Python tracebacks end with
        // the exception)
        let last = err
            .lines()
            .find(|l| l.contains("error"))
            .or_else(|| err.lines().rev().find(|l| !l.trim().is_empty()))
            .unwrap_or("")
            .trim();
        Err(format!("{} failed ({}): {last}", Path::new(cmd.get_program()).display(), out.status))
    }
}

/// Outcome of one CGU.
pub struct CguResult {
    pub functions: Vec<FnReport>,
    /// The object was rewritten (some function now runs Lean code).
    pub changed: bool,
    /// The pipeline failed as a whole (all functions fall back).
    pub error: Option<String>,
    /// An error that fails the build (a `lean-backend` run over `FV_FN_TIME_LIMIT`).
    pub fatal: Option<String>,
}

/// data-export names `.LdataN` of the object `c_LdataN` (the dump directory is `c.clif`).
fn obj_name_of(ours: &str) -> String {
    match ours.strip_prefix("c_Ldata") {
        Some(hex) => format!(".Ldata{hex}"),
        None => ours.to_string(),
    }
}

/// The CLIF name of the object symbol `obj` (the inverse of `obj_name_of`).
fn clif_name_of(obj: &str) -> String {
    match obj.strip_prefix(".Ldata") {
        Some(hex) => format!("c_Ldata{hex}"),
        None => obj.to_string(),
    }
}

/// The names a decoded CLIF function declares (`gvN = symbol … %name`, `fnN = … %name(…)`):
/// every symbol its code may reference.
fn clif_decl_names(path: &Path) -> Result<Vec<String>, String> {
    let text = fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
    let mut names = Vec::new();
    for l in text.lines() {
        let t = l.trim_start();
        let Some((lhs, rhs)) = t.split_once(" = ") else { continue };
        let decl = (lhs.starts_with("gv") || lhs.starts_with("fn"))
            && lhs.len() > 2
            && lhs[2..].chars().all(|c| c.is_ascii_digit());
        if !decl {
            continue;
        }
        if let Some((_, n)) = rhs.split_once('%') {
            let end = n.find(|c: char| matches!(c, '(' | ' ' | ',' | ')' | '+' | '-')).unwrap_or(n.len());
            names.push(n[..end].to_string());
        }
    }
    Ok(names)
}

fn fallback_all(funcs: &[(String, Dump)], why: &str) -> Vec<FnReport> {
    funcs
        .iter()
        .map(|(s, d)| FnReport {
            symbol: s.clone(),
            instance: d.instance.clone(),
            status: Status::Fallback,
            reason: Some(why.to_string()),
            normal_returns: false,
            theorem: None,
            about: None,
            unopt_input_opt_level: None,
            midval: None,
        })
        .collect()
}

/// Process one CGU object in place. `id` names the CGU uniquely in the build (unit + object).
pub fn process_object(cfg: &Config, index: &DumpIndex, obj: &Path, id: &str) -> CguResult {
    let syms = match read_syms(obj) {
        Ok(s) => s,
        Err(e) => return CguResult { functions: vec![], changed: false, error: Some(e), fatal: None },
    };
    let mut funcs: Vec<(String, Dump)> = index
        .by_symbol
        .iter()
        .filter(|(s, _)| syms.text.contains_key(*s))
        .map(|(s, d)| (s.clone(), d.clone()))
        .collect();
    funcs.sort_by(|a, b| a.0.cmp(&b.0));
    // debugging aids (docs/USAGE.md, troubleshooting): force functions to fall back
    let (skip, only, pkg_skip) = (filter_env("FV_SKIP"), filter_env("FV_ONLY"), cfg.skip_patterns());
    let mut forced: Vec<FnReport> = Vec::new();
    let all: Vec<Dump> = funcs.iter().map(|(_, d)| d.clone()).collect();
    funcs.retain(|(s, d)| {
        let hit = |pats: &Vec<String>| pats.iter().any(|p| s.contains(p.as_str()) || d.instance.contains(p.as_str()));
        let why = if hit(&pkg_skip) {
            "skipped (package.metadata.fv.skip)"
        } else if hit(&skip) {
            "skipped (FV_SKIP)"
        } else if !only.is_empty() && !hit(&only) {
            "not selected (FV_ONLY)"
        } else {
            return true;
        };
        forced.push(FnReport {
            symbol: s.clone(),
            instance: d.instance.clone(),
            status: Status::Fallback,
            reason: Some(why.into()),
            normal_returns: false,
            theorem: None,
            about: None,
            unopt_input_opt_level: None,
            midval: None,
        });
        false
    });
    let mut res = process_selected(cfg, index, obj, id, &syms, &all, funcs);
    res.functions.extend(forced);
    res
}

fn filter_env(k: &str) -> Vec<String> {
    std::env::var(k).map(|v| v.split(',').filter(|p| !p.is_empty()).map(String::from).collect()).unwrap_or_default()
}

/// Why the compiled object's undefined references cannot bind in cg_clif's object (`None`:
/// they all resolve to cg_clif's definitions, cg_clif's own imports, or the runtime helpers),
/// plus the local symbols it references (for the symbol surgery).
fn ref_problem(o: &Path, syms: &ObjSyms) -> Result<(Option<String>, Vec<String>), String> {
    let f = read_syms(o)?;
    let mut bad: Option<String> = None;
    let mut locals = Vec::new();
    for u in &f.undefined {
        let n = obj_name_of(u);
        if syms.local_count.get(&n).copied().unwrap_or(0) > 1 {
            bad = Some(format!("references `{n}`, defined locally more than once in cg_clif's object"));
        } else if syms.local_count.contains_key(&n) {
            locals.push(n);
        } else if !(syms.defined.contains(&n) || syms.undefined.contains(&n) || RUNTIME_HELPERS.contains(&n.as_str())) {
            // e.g. a callee or static only the unoptimised code uses: Cranelift's optimiser
            // removed cg_clif's own reference (the retry of `compile_one`)
            bad = Some(format!("references `{u}`, which cg_clif's object neither defines nor references (unused by its optimised code)"));
        }
        if bad.is_some() {
            break;
        }
    }
    Ok((bad, locals))
}

/// Why the compiled object's undefined references cannot bind in cg_clif's object (`None`:
/// they all resolve to cg_clif's definitions, cg_clif's own imports, or the runtime helpers).
fn missing_ref(o: &Path, syms: &ObjSyms) -> Option<String> {
    ref_problem(o, syms).ok().and_then(|(bad, _)| bad)
}

/// Hold one of the build's `cfg.jobs` lean-backend slots (`<tmp>/slots/<k>.lock`, an advisory
/// file lock released when the file is dropped or the process dies). cargo runs many rustc
/// processes at once once dependencies are compiled too, so the limit must hold across all
/// fv-rustc processes of the build, not per codegen unit. `None`: no lock directory (the run
/// proceeds unthrottled).
fn backend_slot(cfg: &Config) -> Option<fs::File> {
    let dir = cfg.tmp_dir.join("slots");
    fs::create_dir_all(&dir).ok()?;
    let n = cfg.jobs.max(1);
    let mut files: Vec<fs::File> = (0..n)
        .filter_map(|k| fs::OpenOptions::new().create(true).truncate(false).write(true).open(dir.join(format!("{k}.lock"))).ok())
        .collect();
    if files.is_empty() {
        return None;
    }
    loop {
        if let Some(i) = files.iter().position(|f| f.try_lock().is_ok()) {
            return Some(files.swap_remove(i));
        }
        std::thread::sleep(std::time::Duration::from_millis(15));
    }
}

/// Compile one function from its decoded `.unopt.clif` dump into `o/f{i}.o`.
///
/// Retry: the unoptimised CLIF may reference symbols that cg_clif's object neither defines nor
/// references — the unoptimised dump still holds paths Cranelift's optimiser removed (e.g. a
/// call of a panic function only a dead path makes). The optimised dump (`{stem}.opt.clif`,
/// decoded the same way) matches the code cg_clif actually emitted, so compiling it references
/// only symbols the object binds. Only such references trigger the retry; a failing retry keeps
/// the unopt result (whose reference check then reports the fallback reason). A dump that does
/// not decode (`clif-decode` wrote `X.clif.err`) falls back with the decoder's reason.
fn compile_one(
    cfg: &Config,
    syms: &ObjSyms,
    split: &Path,
    outdir: &Path,
    i: usize,
    d: &Dump,
    sym: &str,
) -> Compiled {
    let run_backend = |input: &Path, out: &Path, midval: Option<&Path>| -> Compiled {
        if !input.exists() {
            let err = input.with_file_name(format!("{}.err", input.file_name().unwrap_or_default().to_string_lossy()));
            return Compiled::Fallback(match fs::read_to_string(&err) {
                Ok(why) => format!("decode: {}", why.trim()),
                Err(_) => format!("{}: no decoded CLIF", input.display()),
            });
        }
        if let Some(why) = abi_guard(input) {
            return Compiled::Fallback(why);
        }
        // `--personality`: functions with landing pads (`try_call`) get cg_clif's LSDA and
        // personality (`rust_eh_personality`, which cg_clif hard-codes too)
        let slot = backend_slot(cfg);
        let mut cmd = Command::new(cfg.lean_backend());
        cmd.arg(input)
            .arg(out)
            .args(cfg.mode.backend_args())
            .args(["--personality", "rust_eh_personality"])
            // `--lean-link` keeps cg_clif's code for an unverified function: one unverified
            // before it is compiled is not compiled (#1074)
            .args(cfg.lean_link.then_some("--skip-unverified"));
        // #1119: Cranelift's optimised function, compiled when lean-backend decides the mid-end
        // validator's re-check on the pair (else the `.unopt.clif`, as without it)
        if let Some(g) = midval {
            cmd.arg("--midval-opt").arg(g);
        }
        // `--keep-temps`: keep the register allocator's answers next to the object (`cargo fv
        // link-proof` and `lean-link` rebuild the allocations from them in Lean): lean-backend
        // writes regalloc2's answers to `$FV_RA_OUT` (`FVTest/Backend/Main.lean`)
        if cfg.keep_link() {
            cmd.env(crate::linkproof::RA_OUT, out.with_extension("ra.json"));
        }
        match output_with_limit(&mut cmd, cfg.fn_time_limit) {
            Ok(Run::Done(o)) => {
                drop(slot);
                classify(cfg, &String::from_utf8_lossy(&o.stderr), o.status.success(), out, sym, input)
            }
            Ok(Run::TimedOut) => Compiled::TimedOut,
            Err(e) => Compiled::Fallback(format!("cannot run lean-backend: {e}")),
        }
    };
    let out = outdir.join(format!("f{i}.o"));
    let opt = split.join(format!("{}.opt.clif", d.stem));
    // #1119: the mid-end validator in plain mode without `--lean-link` (whose linker and
    // link-check do not re-decide the pair yet), for a function cg_clif optimised
    let midval = (cfg.midval
        && cfg.mode == Mode::Plain
        && !cfg.lean_link
        && !d.opt_level.is_empty()
        && d.opt_level != "none"
        && opt.exists())
    .then_some(opt.as_path());
    let c = run_backend(&split.join(format!("{}.unopt.clif", d.stem)), &out, midval);
    if let Compiled::Ok { .. } = &c {
        if let Some(why) = missing_ref(&out, syms) {
            if why.contains("neither defines nor references") && opt.exists() {
                let out_opt = outdir.join(format!("f{i}.opt.o"));
                let c2 = run_backend(&opt, &out_opt, None);
                if let Compiled::Ok { obj, unverified, normal_returns, theorem, clif, .. } = c2 {
                    if missing_ref(&obj, syms).is_none() {
                        // the theorem is about the function as Cranelift's optimiser left it
                        let theorem = theorem.map(|v| Verdict {
                            about: format!("{}, compiled from cg_clif's optimised dump (.opt.clif)", v.about),
                            ..v
                        });
                        return Compiled::Ok { obj, unverified, normal_returns, theorem, clif, midval: None };
                    }
                }
            }
        }
    }
    c
}

/// The build's error for the function `instance` (object symbol `symbol`) whose `lean-backend`
/// run exceeded `FV_FN_TIME_LIMIT` (`secs`).
pub fn time_limit_error(secs: u64, symbol: &str, instance: &str) -> String {
    format!(
        "{instance} ({symbol}): lean-backend did not finish within FV_FN_TIME_LIMIT={secs} s; the build stops \
         (a time limit is never a fallback: what is verified must not depend on the machine's load). \
         Skip the function with `[package.metadata.fv] skip = [\"{symbol}\"]` or `FV_SKIP={symbol}`, \
         raise FV_FN_TIME_LIMIT, or report it at https://github.com/eth-act/clifv/issues"
    )
}

/// A `lean-backend` run: its output, or killed at the time limit.
pub enum Run {
    Done(std::process::Output),
    TimedOut,
}

/// `cmd.output()`, killed (`SIGKILL`) after `limit_secs` seconds of wall time (0: no limit).
/// A watchdog thread waits for the end of the run up to the limit and kills the process when
/// it has not ended; the run counts as timed out only when the watchdog fired and the process
/// died of that signal.
pub fn output_with_limit(cmd: &mut Command, limit_secs: u64) -> std::io::Result<Run> {
    use std::os::unix::process::ExitStatusExt;
    use std::process::Stdio;
    use std::sync::mpsc;
    if limit_secs == 0 {
        return cmd.output().map(Run::Done);
    }
    let child = cmd.stdin(Stdio::null()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn()?;
    let pid = child.id().to_string();
    let (done, ended) = mpsc::channel::<()>();
    let watchdog = std::thread::spawn(move || {
        // the child is not reaped before `done` is sent, so its pid cannot be reused meanwhile
        if let Err(mpsc::RecvTimeoutError::Timeout) = ended.recv_timeout(std::time::Duration::from_secs(limit_secs)) {
            let _ = Command::new("kill").args(["-KILL", &pid]).stdout(Stdio::null()).stderr(Stdio::null()).status();
            return true;
        }
        false
    });
    let out = child.wait_with_output();
    let _ = done.send(());
    let fired = watchdog.join().unwrap_or(false);
    let out = out?;
    if fired && out.status.signal() == Some(9) {
        return Ok(Run::TimedOut);
    }
    Ok(Run::Done(out))
}

/// `all`: every function of the CGU (the decoding input: the unit's declarations are read from
/// all its dumps); `funcs`: the ones to compile.
fn process_selected(
    cfg: &Config,
    index: &DumpIndex,
    obj: &Path,
    id: &str,
    syms: &ObjSyms,
    all: &[Dump],
    funcs: Vec<(String, Dump)>,
) -> CguResult {
    if funcs.is_empty() {
        return CguResult { functions: vec![], changed: false, error: None, fatal: None };
    }
    let tag = tag_of(id);
    let work = cfg.tmp_dir.join(&tag);
    let _ = fs::remove_dir_all(&work);
    let r = process_in(cfg, index, obj, syms, all, &funcs, &tag, &work);
    if !cfg.keep_temps {
        if cfg.bin_check {
            remove_objects(&work);
        } else {
            let _ = fs::remove_dir_all(&work);
        }
    }
    match r {
        Ok((functions, changed)) => CguResult { functions, changed, error: None, fatal: None },
        Err(CguFail::Fallback(e)) => CguResult { functions: fallback_all(&funcs, &e), changed: false, error: Some(e), fatal: None },
        Err(CguFail::Fatal(e)) => CguResult { functions: fallback_all(&funcs, &e), changed: false, error: None, fatal: Some(e) },
    }
}

/// Remove the object files of a codegen unit's work directory (recursively), keeping the text
/// files the binary check reads (`fv-link.json`, the compiled CLIF, the regalloc outputs, the
/// data objects).
fn remove_objects(dir: &Path) {
    let Ok(rd) = fs::read_dir(dir) else { return };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            remove_objects(&p);
        } else if p.extension().is_some_and(|x| x == "o") {
            let _ = fs::remove_file(&p);
        }
    }
}

/// Known calling-convention differences between the Lean backend and Cranelift (cg_clif's code,
/// the other side of every call between a Lean-compiled and a fallback function): (text of a
/// parameter in a signature, reason). A function whose own signature or any callee declaration
/// (`fnN = …`, `sigN = …`) contains the text falls back. Empty today.
///
/// History: `("i64 sret", …)` until f52e514: lean-backend passed the arguments after an sret
/// pointer from x1, Cranelift from x0 (sret in x8 takes no argument register);
/// examples/fv-demo's `sret_interop` test is the regression test.
const ABI_MISMATCHES: &[(&str, &str)] = &[];

fn abi_guard(input: &Path) -> Option<String> {
    if ABI_MISMATCHES.is_empty() {
        return None;
    }
    let text = fs::read_to_string(input).ok()?;
    let body = text.split_once("\nfunction ").map(|(_, b)| b).unwrap_or(&text);
    let sig = body.lines().next().unwrap_or("");
    let decls = || {
        body.lines().filter(|l| {
            let t = l.trim_start();
            (t.starts_with("fn") || t.starts_with("sig")) && t.contains(" = ")
        })
    };
    for (pat, why) in ABI_MISMATCHES {
        if sig.contains(pat) {
            return Some(format!("ABI mismatch with Cranelift: {why}"));
        }
        if decls().any(|l| l.contains(pat)) {
            return Some(format!("ABI mismatch with Cranelift (a callee's signature): {why}"));
        }
    }
    None
}

/// `--trap-replaced`: overwrite cg_clif's (now dead) code of the given functions with `udf`
/// words, so executing it would crash: the tests then show that every call reaches the Lean
/// code. (A relocation inside the range still patches bits 25:0 of its word; the result stays
/// in the reserved/unallocated encoding space, op0 = 000x.)
fn trap_bodies(obj: &Path, names: &[String]) -> Result<(), String> {
    let mut data = fs::read(obj).map_err(|e| format!("{}: {e}", obj.display()))?;
    let mut patches: Vec<(usize, usize)> = Vec::new();
    {
        let file = object::File::parse(&*data).map_err(|e| format!("{}: {e}", obj.display()))?;
        let want: BTreeSet<&str> = names.iter().map(String::as_str).collect();
        for sym in file.symbols() {
            let Ok(n) = sym.name() else { continue };
            if !want.contains(n) || sym.is_undefined() {
                continue;
            }
            let Some(si) = sym.section_index() else { continue };
            let sec = file.section_by_index(si).map_err(|e| e.to_string())?;
            let Some((off, size)) = object::read::ObjectSection::file_range(&sec) else { continue };
            let (start, len) = (sym.address(), sym.size());
            if start + len > size {
                return Err(format!("`{n}` extends past its section"));
            }
            patches.push(((off + start) as usize, len as usize));
        }
    }
    for (at, len) in patches {
        for w in data[at..at + len].chunks_mut(4) {
            let udf = 0x0000_00f0u32.to_le_bytes(); // udf #0xf0
            w.copy_from_slice(&udf[..w.len()]);
        }
    }
    fs::write(obj, data).map_err(|e| format!("{}: {e}", obj.display()))
}

/// How lean-backend classified one function (`normal_returns`: a `try_call` function the
/// theorem covers for its normal returns only; `theorem`: the per-function theorem lean-backend
/// named with every checkable premise decided, and what it is about; `clif`: the file it
/// compiled; `midval`: lean-backend's `--midval-opt` outcome and reason, #1119).
enum Compiled {
    Ok {
        obj: PathBuf,
        unverified: Option<String>,
        normal_returns: bool,
        theorem: Option<Verdict>,
        clif: PathBuf,
        midval: Option<(String, Option<String>)>,
    },
    Fallback(String),
    /// Killed at `FV_FN_TIME_LIMIT`: the build fails ([`time_limit_error`]).
    TimedOut,
}

/// Why a codegen unit was not rewritten: a failure whose functions fall back, or an error that
/// fails the build ([`CguResult::fatal`]).
enum CguFail {
    Fallback(String),
    Fatal(String),
}

impl From<String> for CguFail {
    fn from(e: String) -> CguFail {
        CguFail::Fallback(e)
    }
}

/// The fallback reason of a function `lean-backend` lists unverified (`u`) under `--lean-link`.
fn kept_reason(u: &str) -> String {
    format!("unverified ({u}): cg_clif's code kept under --lean-link")
}

/// lean-backend's verdict line for a verified function (`FVTest/Backend/FnVerdict.lean`):
/// `…: compiled, verified by <theorem> (about <what>; decided: <checks>)[; unwinding by …]` or
/// `…: compiled, verified for normal returns by <theorem> (…)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Verdict {
    pub theorem: String,
    pub about: String,
}

/// The verdict of one `lean-backend` stderr line, if it is a verdict line.
pub(crate) fn verdict_of(line: &str) -> Option<(Verdict, bool)> {
    let (rest, normal) = if let Some((_, r)) = line.split_once(": compiled, verified for normal returns by ") {
        (r, true)
    } else {
        (line.split_once(": compiled, verified by ")?.1, false)
    };
    let (theorem, tail) = rest.split_once(" (about ")?;
    let about = tail.split_once("; decided: ").map(|(a, _)| a).unwrap_or(tail);
    Some((Verdict { theorem: theorem.to_string(), about: about.to_string() }, normal))
}

/// lean-backend's `--midval-opt` line (#1119, `FVTest/Backend/Main.lean`), as (outcome, reason):
/// `…: midval: validated (…), compiled from the optimised dump …` → `validated`;
/// `…: midval: rejected (<why>); compiled from the .unopt.clif as without --midval-opt` →
/// `rejected`, likewise `validated, not composed (<why>)` → `not composed` and
/// `not attempted (<why>)` → `not attempted`.
pub(crate) fn midval_of(line: &str) -> Option<(String, Option<String>)> {
    let rest = line.split_once(": midval: ")?.1;
    if rest.starts_with("validated (") {
        return Some(("validated".into(), None));
    }
    let rest = rest.strip_suffix("; compiled from the .unopt.clif as without --midval-opt").unwrap_or(rest);
    let (outcome, why) = rest.split_once(" (").unwrap_or((rest, ""));
    let outcome = outcome.strip_prefix("validated, ").unwrap_or(outcome);
    let why = why.strip_suffix(')').unwrap_or(why);
    Some((outcome.to_string(), (!why.is_empty()).then(|| why.to_string())))
}

fn classify(cfg: &Config, stderr: &str, ok: bool, out: &Path, symbol: &str, input: &Path) -> Compiled {
    let strip = |l: &str| -> String {
        // `lean-backend: <input>: %name: …` / `lean-backend: <input>: …`
        let l = l.strip_prefix("lean-backend: ").unwrap_or(l);
        let l = l.split_once(".clif: ").map(|(_, r)| r).unwrap_or(l);
        l.to_string()
    };
    if !ok {
        let first = stderr.lines().find(|l| !l.trim().is_empty()).map(strip).unwrap_or_default();
        return Compiled::Fallback(format!("lean-backend failed: {first}"));
    }
    // lean-backend prints the closure warnings before the per-function reasons; its own
    // reason (e.g. "outside clif-subset-v2 E") is the more precise one, so it wins.
    let mut unverified: Option<String> = None;
    let mut outside_closure: Option<String> = None;
    let mut normal_returns = false;
    let mut theorem: Option<Verdict> = None;
    let mut midval: Option<(String, Option<String>)> = None;
    for l in stderr.lines() {
        // `--midval-opt` (#1119): its own line, whose reason may quote any other line's text
        if let Some(m) = midval_of(l) {
            midval = Some(m);
            continue;
        }
        // `--skip-unverified`: the reason the compiled function would get, and its fallback
        if let Some((_, rest)) = l.split_once(": not compiled (--skip-unverified), unverified (") {
            let u = match rest.split_once("): ") {
                Some(("validation budget", why)) => format!("validation budget: {why}"),
                Some((_, why)) => why.to_string(),
                None => rest.to_string(),
            };
            return Compiled::Fallback(kept_reason(&u));
        }
        if let Some((v, normal)) = verdict_of(l) {
            normal_returns |= normal;
            theorem.get_or_insert(v);
        }
        if let Some((_, why)) = l.split_once(": unsupported: ") {
            return Compiled::Fallback(format!("unsupported: {why}"));
        }
        if let Some((_, why)) = l.split_once(": compiled, unverified (outside backend_correct): ") {
            unverified.get_or_insert(why.to_string());
        } else if let Some((_, why)) = l.split_once(": compiled, unverified (validation budget): ") {
            unverified.get_or_insert(format!("validation budget: {why}"));
        } else if l.contains("fired outside the emitter-subset closure") {
            let r = strip(l);
            outside_closure.get_or_insert(format!("ISLE {r}"));
        } else if l.contains(": encoding failed: ") {
            return Compiled::Fallback(strip(l));
        }
    }
    let mut unverified = unverified.or(outside_closure);
    match read_syms(out) {
        Ok(s) if s.text.get(symbol) == Some(&true) => {}
        Ok(_) => return Compiled::Fallback("lean-backend emitted no code for the function".into()),
        Err(e) => return Compiled::Fallback(format!("lean-backend output unreadable: {e}")),
    }
    // verified only with a named theorem (fail closed: a compiled function without a verdict line
    // is outside every theorem lean-backend decided)
    if unverified.is_none() && theorem.is_none() {
        unverified = Some("lean-backend named no per-function theorem".into());
    }
    if cfg.mode == Mode::Opt {
        let why = "--opt: the Lean mid-end ran unproven simplify rules";
        unverified = Some(match unverified {
            Some(u) => format!("{u}; {why}"),
            None => why.into(),
        });
    }
    if unverified.is_some() {
        theorem = None;
        normal_returns = false;
    }
    Compiled::Ok { obj: out.to_path_buf(), unverified, normal_returns, theorem, clif: input.to_path_buf(), midval }
}

fn write_list(path: &Path, items: impl IntoIterator<Item = String>) -> Result<(), String> {
    let mut s = String::new();
    for i in items {
        s.push_str(&i);
        s.push('\n');
    }
    fs::write(path, s).map_err(|e| format!("{}: {e}", path.display()))
}

/// A relocatable object whose `.text` is one zero word (`udf #0`), without symbols: the gap
/// word after each Lean-compiled function under `--lean-link`.
fn gap_object(cfg: &Config, work: &Path) -> Result<PathBuf, String> {
    let bin = work.join("gap.bin");
    let o = work.join("gap.o");
    if o.is_file() {
        // the unit's (`lean_variant` builds after it)
        return Ok(o);
    }
    fs::write(&bin, [0u8; 4]).map_err(|e| format!("{}: {e}", bin.display()))?;
    run(Command::new(&cfg.objcopy)
        .args(["-I", "binary", "-O", "elf64-littleaarch64", "--rename-section", ".data=.text,alloc,load,readonly,code,contents", "--strip-all"])
        .arg(&bin)
        .arg(&o))?;
    Ok(o)
}

/// The alignment of the function object `o`'s `.text` (`lean-backend`: 8 for a function with a
/// literal pool, as Cranelift's `MachBuffer` aligns its code to its constants'; else 4). Under
/// `--lean-link`, `ld -r` starts the function at that alignment in the program part and the
/// Lean linker's placement follows it (`Link.offsA`, `cargo fv link-proof`'s `aligns`, #1061).
pub fn text_align(o: &Path) -> Result<u64, String> {
    let data = fs::read(o).map_err(|e| format!("{}: {e}", o.display()))?;
    let file = object::File::parse(&*data).map_err(|e| format!("{}: {e}", o.display()))?;
    Ok(file
        .sections()
        .filter(|s| object::read::ObjectSection::name(s) == Ok(".text"))
        .map(|s| object::read::ObjectSection::align(&s))
        .max()
        .unwrap_or(4))
}

/// The unit's Lean-compiled functions (`--lean-link`): one line `symbol<TAB>object` each, in
/// placement order ([`lean_variant`]).
pub const LEAN_FUNCS: &str = "lean-funcs.txt";

/// The Lean code of the functions `fns` (symbol, object) as one relocatable object `out` in the
/// work directory: `ld -r` of the objects (with `--lean-link` each followed by a zero word, the
/// Lean linker's placement `Link.offsA`: each function at its object's `.text` alignment, zeros
/// before it, the gap word after it, so that `ld -r` lays the code out as the Lean linker places
/// it), the unit's renaming `renames` (data names too, and the names the code references under
/// another spelling, [`obj_name_of`]) and a marker `__fvlean$<final>` at each function. `prefix`
/// names the work files. Returns the CLIF names of the code → their final symbol names
/// (`cargo fv link-proof`).
fn lean_object(
    cfg: &Config,
    work: &Path,
    out: &Path,
    prefix: &str,
    fns: &[(String, PathBuf)],
    renames: &BTreeMap<String, String>,
) -> Result<BTreeMap<String, String>, String> {
    let final_name = |s: &str| renames.get(s).cloned().unwrap_or_else(|| s.to_string());
    let mut inputs: Vec<PathBuf> = Vec::new();
    if cfg.lean_link {
        let pad = gap_object(cfg, work)?;
        for (_, o) in fns {
            inputs.push(o.clone());
            inputs.push(pad.clone());
        }
    } else {
        inputs.extend(fns.iter().map(|(_, o)| o.clone()));
    }
    // the inputs through a response file: a large codegen unit (std's, `--build-std`) has more
    // objects than one command line holds
    let inputs_rsp = work.join(format!("{prefix}-inputs.rsp"));
    write_list(
        &inputs_rsp,
        inputs.iter().map(|p| format!("\"{}\"", p.display().to_string().replace('\\', "\\\\").replace('"', "\\\""))),
    )?;
    run(Command::new(&cfg.rust_lld).args(["-flavor", "gnu", "-r", "-o"]).arg(out).arg(format!("@{}", inputs_rsp.display())))?;
    let syms = read_syms(out)?;
    let mut redef: Vec<String> = renames.iter().map(|(a, b)| format!("{a} {b}")).collect();
    let mut clif_names: BTreeMap<String, String> = fns.iter().map(|(s, _)| (s.clone(), final_name(s))).collect();
    for u in &syms.undefined {
        let n = obj_name_of(u);
        clif_names.insert(u.clone(), final_name(&n));
        if n != *u {
            redef.push(format!("{u} {}", final_name(&n)));
        }
    }
    let redef_path = work.join(format!("redefine-{prefix}.txt"));
    write_list(&redef_path, redef)?;
    run(Command::new(&cfg.objcopy).arg(format!("--redefine-syms={}", redef_path.display())).arg(out))?;
    let syms = read_syms(out)?;
    let data = fs::read(out).map_err(|e| format!("{}: {e}", out.display()))?;
    let file = object::File::parse(&*data).map_err(|e| format!("{}: {e}", out.display()))?;
    let mut markers = Vec::new();
    for (s, _) in fns {
        let n = final_name(s);
        let Some(&(si, v)) = syms.at.get(&n) else {
            return Err(format!("internal: `{n}` missing from the merged Lean object"));
        };
        let sec = object::read::ObjectSection::name(
            &object::read::Object::section_by_index(&file, object::SectionIndex(si))
                .map_err(|e| format!("{}: {e}", out.display()))?,
        )
        .map_err(|e| format!("{}: {e}", out.display()))?
        .to_string();
        // global here (llvm-objcopy appends added symbols after the globals, so a local one
        // breaks the symbol table order); localised with the renamed symbols after the merge
        markers.push(format!("--add-symbol={MARKER}{n}={sec}:{v},global,function"));
    }
    let rsp = work.join(format!("{prefix}-markers.rsp"));
    write_list(&rsp, markers)?;
    run(Command::new(&cfg.objcopy).arg(format!("@{}", rsp.display())).arg(out))?;
    Ok(clif_names)
}

/// `--lean-link --verified` (T3c): the unit's Lean object without the functions whose final
/// symbol names `exclude` lists (they fail a per-function input condition of the executable's
/// compiler theorem; `lake exe lean-link` lists them): built from the unit's per-function objects
/// ([`LEAN_FUNCS`]) with the unit's renaming (`redefine.txt`), so that the excluded functions'
/// symbols bind to cg_clif's (weak) copies. `None` when the unit has no excluded function (its
/// `lean.o` stands). Written under a name of the exclusion set, atomically (other executables'
/// links read the unit too).
pub fn lean_variant(cfg: &Config, work: &Path, exclude: &BTreeSet<String>) -> Result<Option<PathBuf>, String> {
    let read = |name: &str| -> Result<String, String> {
        let p = work.join(name);
        fs::read_to_string(&p).map_err(|e| format!("{}: {e}", p.display()))
    };
    let renames: BTreeMap<String, String> = read("redefine.txt")?
        .lines()
        .filter_map(|l| l.split_once(' ').map(|(a, b)| (a.to_string(), b.to_string())))
        .collect();
    let fns: Vec<(String, PathBuf)> = read(LEAN_FUNCS)?
        .lines()
        .filter_map(|l| l.split_once('\t').map(|(s, o)| (s.to_string(), PathBuf::from(o))))
        .collect();
    let final_name = |s: &str| renames.get(s).cloned().unwrap_or_else(|| s.to_string());
    let keep: Vec<(String, PathBuf)> = fns.iter().filter(|(s, _)| !exclude.contains(&final_name(s))).cloned().collect();
    if keep.len() == fns.len() {
        return Ok(None);
    }
    let tag = tag_of(&exclude.iter().cloned().collect::<Vec<_>>().join("\n"));
    let out = work.join(format!("lean-x{tag}.o"));
    if out.is_file() {
        return Ok(Some(out));
    }
    let prefix = format!("lean-x{tag}-{}", std::process::id());
    let tmp = work.join(format!("{prefix}.o"));
    lean_object(cfg, work, &tmp, &prefix, &keep, &renames)?;
    fs::rename(&tmp, &out).map_err(|e| format!("{}: {e}", out.display()))?;
    Ok(Some(out))
}

fn process_in(
    cfg: &Config,
    index: &DumpIndex,
    obj: &Path,
    syms: &ObjSyms,
    all: &[Dump],
    funcs: &[(String, Dump)],
    tag: &str,
    work: &Path,
) -> Result<(Vec<FnReport>, bool), CguFail> {
    // cg_clif's dumps of the CGU's functions: links to them, copies when `cargo fv link-proof`
    // reads them later (`--keep-temps`: the bundle names the dump each function was compiled
    // from, and cargo may rewrite the originals)
    let clif = work.join("c.clif");
    fs::create_dir_all(&clif).map_err(|e| format!("{}: {e}", clif.display()))?;
    for d in all {
        for ext in ["unopt.clif", "opt.clif"] {
            let src = index.dir.join(format!("{}.{ext}", d.stem));
            let to = clif.join(format!("{}.{ext}", d.stem));
            if !src.exists() {
                continue;
            }
            if cfg.keep_link() {
                fs::copy(&src, &to).map(|_| ()).map_err(|e| format!("copy {}: {e}", src.display()))?;
            } else {
                std::os::unix::fs::symlink(&src, &to).map_err(|e| format!("symlink {}: {e}", src.display()))?;
            }
        }
    }
    // 2. the object's data objects (for `cargo fv link-proof`), the decoded functions
    run(Command::new(cfg.data_export()).arg(obj).arg("--out").arg(work.join("data.clif")))?;
    let split = work.join("split");
    run(Command::new(cfg.decode()).arg(&clif).arg("unopt").arg(&split).arg("--split"))?;
    // The optimised dumps: best effort — a failure only disables the retry of `compile_one`
    // (the unopt compilation and its fallback reason are unaffected).
    let split_opt = work.join("split-opt");
    match run(Command::new(cfg.decode()).arg(&clif).arg("opt").arg(&split_opt).arg("--split")) {
        Ok(_) => {
            for e in fs::read_dir(&split_opt).map_err(|e| format!("{}: {e}", split_opt.display()))?.flatten() {
                let to = split.join(e.file_name());
                fs::rename(e.path(), &to).map_err(|err| format!("{}: {err}", to.display()))?;
            }
        }
        Err(e) => eprintln!("cargo fv: warning: {tag}: the .opt.clif dumps do not decode ({e})"),
    }

    // 3. one lean-backend run per function, `cfg.jobs` at a time
    let outdir = work.join("o");
    fs::create_dir_all(&outdir).map_err(|e| format!("{}: {e}", outdir.display()))?;
    let next = AtomicUsize::new(0);
    let mut slots: Vec<Option<Compiled>> = (0..funcs.len()).map(|_| None).collect();
    std::thread::scope(|sc| {
        let workers: Vec<_> = (0..cfg.jobs.max(1).min(funcs.len()))
            .map(|_| {
                sc.spawn(|| {
                    let mut done = Vec::new();
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        if i >= funcs.len() {
                            break done;
                        }
                        let (sym, d) = &funcs[i];
                        done.push((i, compile_one(cfg, syms, &split, &outdir, i, d, sym)));
                    }
                })
            })
            .collect();
        for w in workers {
            for (i, c) in w.join().expect("lean-backend worker panicked") {
                slots[i] = Some(c);
            }
        }
    });
    let results: Vec<Compiled> = slots.into_iter().map(|c| c.expect("every function compiled")).collect();

    // 4. every reference of our code must be one the object already makes
    let mut reports = Vec::new();
    let mut ours: Vec<(String, PathBuf)> = Vec::new();
    // `--keep-temps`: per Lean-compiled function, what `cargo fv link-proof` needs
    let mut link_fns: Vec<serde_json::Value> = Vec::new();
    let mut referenced_locals: BTreeSet<String> = BTreeSet::new();
    // `--lean-link`: the names the compiled CLIF declares; the Lean linker reads the functions
    // from their dumps (`Front.buildSpec`), so each needs its linked name even when the Lean
    // mid-end (`--opt-proven-only`) removed the code referencing it
    let mut declared: BTreeSet<String> = BTreeSet::new();
    for ((sym, d), c) in funcs.iter().zip(results) {
        // #1119 (`from_unopt`): a Lean-compiled function compiled from its `.unopt.clif` (not the
        // `.opt.clif` retry, not the validated optimised function of `--midval`); with the dump's
        // header saying cg_clif optimised it, stock compiles Cranelift's optimised function while
        // the theorem is about the unoptimised one
        let mut report = |status: Status,
                          reason: Option<String>,
                          normal_returns: bool,
                          theorem: Option<Verdict>,
                          from_unopt: bool,
                          midval: Option<(String, Option<String>)>| {
            let (theorem, about) = match theorem {
                Some(v) => (Some(v.theorem), Some(v.about)),
                None => (None, None),
            };
            let optimised = from_unopt && !d.opt_level.is_empty() && d.opt_level != "none";
            reports.push(FnReport {
                symbol: sym.clone(),
                instance: d.instance.clone(),
                status,
                reason,
                normal_returns,
                theorem,
                about,
                unopt_input_opt_level: optimised.then(|| d.opt_level.clone()),
                midval: midval.map(|(outcome, reason)| MidvalReport { outcome, reason, opt_level: d.opt_level.clone() }),
            })
        };
        match c {
            Compiled::Fallback(why) => report(Status::Fallback, Some(why), false, None, false, None),
            Compiled::TimedOut => return Err(CguFail::Fatal(time_limit_error(cfg.fn_time_limit, sym, &d.instance))),
            Compiled::Ok { obj: o, unverified, normal_returns, theorem, clif, midval } => {
                let validated = midval.as_ref().is_some_and(|(o, _)| o == "validated");
                let from_unopt = clif.ends_with(format!("{}.unopt.clif", d.stem)) && !validated;
                let f = read_syms(&o)?;
                let (mut bad, locals) = ref_problem(&o, syms)?;
                let extra: Vec<&String> = f.text.iter().filter(|(n, g)| **g && *n != sym).map(|(n, _)| n).collect();
                if bad.is_none() && !extra.is_empty() {
                    bad = Some(format!("our object defines other symbols too ({})", extra[0]));
                }
                if bad.is_none() && syms.local_count.get(sym).copied().unwrap_or(0) > 1 {
                    bad = Some("the function's name is defined locally more than once in cg_clif's object".into());
                }
                // `--lean-link`: the region holds verified code only; an unverified function
                // keeps cg_clif's code (the outside part)
                if bad.is_none() && cfg.lean_link {
                    if let Some(u) = &unverified {
                        bad = Some(kept_reason(u));
                    }
                }
                match bad {
                    Some(b) => report(Status::Fallback, Some(b), false, None, false, None),
                    None => {
                        referenced_locals.extend(locals);
                        if cfg.lean_link {
                            for n in clif_decl_names(&clif)? {
                                let o = obj_name_of(&n);
                                if syms.local_count.get(&o) == Some(&1) {
                                    referenced_locals.insert(o);
                                }
                                declared.insert(n);
                            }
                        }
                        // the dump the compiled (decoded) file came from: same file name
                        let dump = clif.file_name().map(|n| work.join("c.clif").join(n)).unwrap_or_default();
                        link_fns.push(serde_json::json!({
                            "symbol": sym,
                            "dump": dump,
                            "ra": o.with_extension("ra.json"),
                            "verified": unverified.is_none(),
                            "reason": unverified,
                            // where `ld -r` starts it in the program part (`--lean-link`, #1061)
                            "align": text_align(&o)?,
                        }));
                        ours.push((sym.clone(), o));
                        match unverified {
                            Some(u) => report(Status::Unverified, Some(u), false, None, from_unopt, midval),
                            None => report(Status::Verified, None, normal_returns, theorem, from_unopt, midval),
                        }
                    }
                }
            }
        }
    }
    if ours.is_empty() {
        return Ok((reports, false));
    }

    // 5. symbol surgery
    let objcopy = |args: &[String], file: &Path| -> Result<(), String> {
        run(Command::new(&cfg.objcopy).args(args).arg(file)).map(|_| ())
    };
    let uname = |l: &str| format!("__fv_{tag}_{}", l.trim_start_matches('.'));
    // local symbols of obj our code defines or references → unique global names
    let mut renames: BTreeMap<String, String> = BTreeMap::new();
    for (s, _) in &ours {
        if syms.text.get(s) == Some(&false) {
            renames.insert(s.clone(), uname(s));
        }
    }
    for l in &referenced_locals {
        renames.insert(l.clone(), uname(l));
    }
    let final_name = |s: &str| renames.get(s).cloned().unwrap_or_else(|| s.to_string());

    let cg = work.join("cgclif.o");
    fs::copy(obj, &cg).map_err(|e| format!("{}: {e}", obj.display()))?;
    let redef = work.join("redefine.txt");
    write_list(&redef, renames.iter().map(|(a, b)| format!("{a} {b}")))?;
    let glob = work.join("globalize.txt");
    write_list(&glob, renames.values().cloned())?;
    let weak = work.join("weaken.txt");
    write_list(&weak, ours.iter().map(|(s, _)| final_name(s)))?;
    if !renames.is_empty() {
        objcopy(&[format!("--redefine-syms={}", redef.display())], &cg)?;
    }
    objcopy(
        &[format!("--globalize-symbols={}", glob.display()), format!("--weaken-symbols={}", weak.display())],
        &cg,
    )?;

    if cfg.trap_replaced {
        trap_bodies(&cg, &ours.iter().map(|(s, _)| final_name(s)).collect::<Vec<_>>())?;
    }

    // our functions: one relocatable object, same renaming (data names too), markers
    let lean = work.join("lean.o");
    let mut clif_names = lean_object(cfg, work, &lean, "lean", &ours, &renames)?;
    for n in &declared {
        clif_names.entry(n.clone()).or_insert_with(|| final_name(&obj_name_of(n)));
    }
    if cfg.lean_link {
        // what `lean_variant` needs to build the object again without some functions
        write_list(&work.join(LEAN_FUNCS), ours.iter().map(|(s, o)| format!("{s}\t{}", o.display())))?;
    }

    if cfg.lean_link {
        // the Lean linker links our code at the executable's link (`leanlink`): the codegen
        // unit is cg_clif's object with the renamed symbols global (our code binds to them
        // there) and its copies of our functions weak
        fs::copy(&cg, obj).map_err(|e| format!("{}: {e}", obj.display()))?;
    } else {
        // merge: our strong definitions win over cg_clif's weakened ones
        let merged = work.join("merged.o");
        run(Command::new(&cfg.rust_lld)
            .args(["-flavor", "gnu", "-r", "--unique", "-o"])
            .arg(&merged)
            .arg(&cg)
            .arg(&lean))?;
        // 6. check before localising: each compiled symbol is at its marker
        let m = read_syms(&merged)?;
        for (s, _) in &ours {
            let n = final_name(s);
            let (a, b) = (m.at.get(&n), m.at.get(&format!("{MARKER}{n}")));
            if a.is_none() || a != b {
                return Err(format!("internal: after the merge `{n}` does not resolve to the Lean code").into());
            }
        }
        let loc = work.join("localize.txt");
        write_list(&loc, renames.values().cloned().chain(ours.iter().map(|(s, _)| format!("{MARKER}{}", final_name(s)))))?;
        objcopy(&[format!("--localize-symbols={}", loc.display())], &merged)?;
        fs::copy(&merged, obj).map_err(|e| format!("{}: {e}", obj.display()))?;
    }
    if cfg.keep_link() {
        for f in &mut link_fns {
            let s = f["symbol"].as_str().unwrap_or_default().to_string();
            f["final"] = serde_json::Value::String(final_name(&s));
        }
        // the unit's local symbols (CLIF name, object symbol): two units' local symbols of
        // one name are different symbols (the Lean-built `LinkSpec`'s scoping, `Front.ScopingOk`)
        let locals: Vec<(String, String)> = syms
            .local_count
            .keys()
            .map(|s| (clif_name_of(s), s.clone()))
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let j = serde_json::json!({
            "tag": tag,
            "object": obj.file_name().map(|n| n.to_string_lossy().into_owned()),
            "functions": link_fns,
            "names": clif_names,
            "locals": locals,
        });
        // written whole, then renamed: the link of another crate built in parallel scans every
        // unit's work directory (`leanlink::program_part`) and must never read a partial record
        let p = work.join(crate::linkproof::CGU_FILE);
        let tmp = work.join(format!("{}.tmp", crate::linkproof::CGU_FILE));
        fs::write(&tmp, serde_json::to_string_pretty(&j).unwrap_or_default())
            .and_then(|()| fs::rename(&tmp, &p))
            .map_err(|e| format!("{}: {e}", p.display()))?;
    }
    Ok((reports, true))
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    fn test_config(root: &Path, limit: u64) -> Config {
        Config {
            root: root.to_path_buf(),
            mode: Mode::Plain,
            members: vec![],
            members_only: false,
            skip_deps: vec![],
            report_dir: root.join("units"),
            tmp_dir: root.join("tmp"),
            rust_lld: "rust-lld".into(),
            objcopy: "objcopy".into(),
            ar: "ar".into(),
            jobs: 1,
            keep_temps: false,
            bin_check: false,
            trap_replaced: false,
            lean_link: false,
            lean_link_verified: false,
            lean_ld: false,
            pkg_skip: vec![],
            fn_time_limit: limit,
            midval: false,
        }
    }

    /// #1074: a run over the limit is killed and reported as timed out, at the limit.
    #[test]
    fn run_over_the_limit_is_killed() {
        let t = Instant::now();
        let r = output_with_limit(Command::new("sleep").arg("30"), 1).unwrap();
        assert!(matches!(r, Run::TimedOut));
        assert!(t.elapsed().as_secs() < 10, "killed after {:?}", t.elapsed());
    }

    /// A run within the limit (or without one) gives its output.
    #[test]
    fn run_within_the_limit_is_kept() {
        for limit in [0, 30] {
            let r = output_with_limit(Command::new("sh").args(["-c", "echo out; echo err >&2; exit 3"]), limit).unwrap();
            let Run::Done(o) = r else { panic!("limit {limit}: timed out") };
            assert_eq!(String::from_utf8_lossy(&o.stdout), "out\n");
            assert_eq!(String::from_utf8_lossy(&o.stderr), "err\n");
            assert_eq!(o.status.code(), Some(3));
        }
    }

    /// A process killed by someone else is not a time-limit fallback (its own failure).
    #[test]
    fn foreign_kill_is_not_a_timeout() {
        let r = output_with_limit(Command::new("sh").args(["-c", "kill -KILL $$"]), 30).unwrap();
        let Run::Done(o) = r else { panic!("timed out") };
        assert!(!o.status.success());
    }

    /// A `lean-backend` that does not finish within `FV_FN_TIME_LIMIT` is killed at the limit and
    /// the function is `TimedOut` (never a fallback: `process_in` turns it into the build's
    /// error), whose message names the function and how to skip it.
    #[test]
    fn slow_backend_is_a_build_error() {
        use std::os::unix::fs::PermissionsExt;
        let root = std::env::temp_dir().join(format!("cargo-fv-timelimit-{}", std::process::id()));
        let bin = root.join(".lake/build/bin");
        fs::create_dir_all(&bin).unwrap();
        let backend = bin.join("lean-backend");
        fs::write(&backend, "#!/bin/sh\nexec sleep 30\n").unwrap();
        fs::set_permissions(&backend, fs::Permissions::from_mode(0o755)).unwrap();
        let split = root.join("split");
        let outdir = root.join("o");
        fs::create_dir_all(&split).unwrap();
        fs::create_dir_all(&outdir).unwrap();
        fs::write(split.join("f.unopt.clif"), "function %f() {\nblock0:\n    return\n}\n").unwrap();
        let syms = ObjSyms {
            text: HashMap::new(),
            defined: BTreeSet::new(),
            local_count: HashMap::new(),
            undefined: BTreeSet::new(),
            at: HashMap::new(),
        };
        let d = Dump { stem: "f".into(), instance: "f".into(), opt_level: "none".into() };
        let t = Instant::now();
        let c = compile_one(&test_config(&root, 1), &syms, &split, &outdir, 0, &d, "f");
        assert!(t.elapsed().as_secs() < 10, "killed after {:?}", t.elapsed());
        assert!(matches!(c, Compiled::TimedOut));
        let e = time_limit_error(1, "_RNxC1a1f", "a::f::<u8>");
        assert!(e.starts_with("a::f::<u8> (_RNxC1a1f): lean-backend did not finish within FV_FN_TIME_LIMIT=1 s"));
        assert!(e.contains("skip = [\"_RNxC1a1f\"]") && e.contains("FV_SKIP=_RNxC1a1f"));
        // the same function within the limit: lean-backend's own result
        fs::write(&backend, "#!/bin/sh\necho 'lean-backend: x.clif: %f: unsupported: test' >&2\n").unwrap();
        let c = compile_one(&test_config(&root, 30), &syms, &split, &outdir, 0, &d, "f");
        assert!(matches!(&c, Compiled::Fallback(why) if why == "unsupported: test"));
        fs::remove_dir_all(&root).unwrap();
    }

    /// #1074: a function `lean-backend --skip-unverified` did not compile falls back with the
    /// reason the compiled function gets under `--lean-link`.
    #[test]
    fn skipped_unverified_keeps_the_reason() {
        let root = std::env::temp_dir().join(format!("cargo-fv-skip-{}", std::process::id()));
        let cfg = test_config(&root, 0);
        let (out, input) = (root.join("f0.o"), root.join("f.unopt.clif"));
        for (line, why) in [
            (
                "lean-backend: x.clif: %f: not compiled (--skip-unverified), unverified (validation budget): 9 instructions × values > 1, lowerCheck not run",
                "validation budget: 9 instructions × values > 1, lowerCheck not run",
            ),
            (
                "lean-backend: x.clif: %f: not compiled (--skip-unverified), unverified (outside backend_correct): i128 legalized (outside backend_correct: validation budget: 9 instructions × values > 1, Opt.Legal.checkW not run)",
                "i128 legalized (outside backend_correct: validation budget: 9 instructions × values > 1, Opt.Legal.checkW not run)",
            ),
        ] {
            let c = classify(&cfg, line, true, &out, "f", &input);
            assert!(matches!(&c, Compiled::Fallback(r) if *r == kept_reason(why)), "{line}");
        }
    }

    #[test]
    fn verdict_lines() {
        let l = "lean-backend: x.clif: %f: compiled, verified by E2E.backend_correct_world_niX_semantic_return_pins (about the source function; decided: unverifiedReason? (InSubset), SemanticABI.checkCalls (the route's validator), prepCheck, formsCoveredB, checkAlloc)";
        let (v, normal) = verdict_of(l).expect("a verdict line");
        assert_eq!(v.theorem, "E2E.backend_correct_world_niX_semantic_return_pins");
        assert_eq!(v.about, "the source function");
        assert!(!normal);
        let l = "lean-backend: x.clif: %f: compiled, verified for normal returns by E2E.backend_correct_final_cleanup (about the source function; decided: lowerCheck); try_call: unwinding, landing pads and the LSDA trusted (unwinding check failed: unwCheck)";
        let (v, normal) = verdict_of(l).expect("a verdict line");
        assert_eq!(v.theorem, "E2E.backend_correct_final_cleanup");
        assert!(normal);
        let l = "lean-backend: x.clif: %f: compiled, verified by E2E.backend_correct_pass_cleanup (T := Opt.ConstPhi.run) (about the source function; decided: Opt.ConstPhi.keeps); unwinding by E2E.backend_correct_pass_cleanup_unwind_any (T := Opt.ConstPhi.run) (trusted: …)";
        let (v, _) = verdict_of(l).expect("a verdict line");
        assert_eq!(v.theorem, "E2E.backend_correct_pass_cleanup (T := Opt.ConstPhi.run)");
        // not verdict lines
        assert!(verdict_of("lean-backend: x.clif: %f: compiled, unverified (outside backend_correct): formsCoveredB fails").is_none());
        assert!(verdict_of("lean-backend: x.clif: %f: frameless leaf, backend_correct_final_cleanup_leaf").is_none());
    }

    /// #1119: lean-backend's `--midval-opt` lines (`FVTest/Backend/Main.lean`), and the theorem
    /// line of a validated function.
    #[test]
    fn midval_lines() {
        let v = midval_of("lean-backend: x.unopt.clif: %f: midval: validated (Opt.MidVal.checkCert decided), compiled from the optimised dump x.opt.clif");
        assert_eq!(v, Some(("validated".into(), None)));
        let r = midval_of("lean-backend: x.unopt.clif: %f: midval: rejected (Opt.MidVal.check rejects: rewrite:operand (iadd)); compiled from the .unopt.clif as without --midval-opt");
        assert_eq!(r, Some(("rejected".into(), Some("Opt.MidVal.check rejects: rewrite:operand (iadd)".into()))));
        let n = midval_of("lean-backend: x.unopt.clif: %f: midval: validated, not composed (the compiled g is unverified (x: unsupported: y)); compiled from the .unopt.clif as without --midval-opt");
        assert_eq!(n, Some(("not composed".into(), Some("the compiled g is unverified (x: unsupported: y)".into()))));
        assert!(midval_of("lean-backend: x.clif: %f: unsupported: y").is_none());
        let l = "lean-backend: x.unopt.clif: %f: compiled, verified by E2E.backend_correct_midval_semantic_return_pins (about the source function (.unopt.clif), compiled from cg_clif's optimised dump validated by Opt.MidVal; decided: prepCheck, Opt.MidVal.checkCert (Opt.ConstPhi.run f) g cert (cert: Opt.MidVal.emit))";
        let (v, _) = verdict_of(l).expect("a verdict line");
        assert_eq!(v.theorem, "E2E.backend_correct_midval_semantic_return_pins");
        assert_eq!(v.about, crate::report::MIDVAL_ABOUT);
    }

    /// #1119: the dump's header gives cg_clif's `opt_level` per function (a release build and a
    /// profile raising `opt-level` alike); a dump without one has an empty level.
    #[test]
    fn dump_index_reads_the_opt_level() {
        let dir = std::env::temp_dir().join(format!("cargo-fv-optlevel-{}", std::process::id()));
        fs::create_dir_all(&dir).unwrap();
        let dump = |level: Option<&str>, sym: &str| {
            let set = level.map(|l| format!("set opt_level={l}\n")).unwrap_or_default();
            format!(
                "test compile\nset regalloc_algorithm=backtracking\n{set}set tls_model=elf_gd\ntarget aarch64\n\n\
                 ; symbol {sym}\nfunction u0:0() system_v {{\n; symbol {sym}\n\
                 ; instance Instance {{ def: Item(DefId(0:5 ~ c[fe56]::{sym})), args: [] }}\nblock0:\n    return\n}}\n"
            )
        };
        for (level, sym) in [(Some("speed_and_size"), "fast"), (Some("none"), "plain"), (None, "bare")] {
            fs::write(dir.join(format!("{sym}.unopt.clif")), dump(level, sym)).unwrap();
        }
        let index = DumpIndex::load(&dir).unwrap();
        let level = |s: &str| index.by_symbol[s].opt_level.clone();
        assert_eq!((level("fast"), level("plain"), level("bare")), ("speed_and_size".into(), "none".into(), String::new()));
        assert_eq!(index.by_symbol["fast"].instance, "c::fast");
        fs::remove_dir_all(&dir).unwrap();
    }
}
