//! Per codegen unit: recompile cg_clif's functions with the Lean backend and splice the
//! result into cg_clif's object, in place.
//!
//! For one CGU object `obj` (cg_clif's output) and the crate's CLIF dump directory:
//!
//! 1. The functions of this CGU are the dumps whose `; symbol` is a text symbol defined in
//!    `obj` (cg_clif numbers `u0:N` per CGU module, so a CGU is the unit of normalisation).
//! 2. `clif-data-export` maps every `symbol_value` data reference to its symbol in `obj`
//!    (`.LdataN` or a named static); `normalize.py --split --gvmap` writes one reader-clean
//!    CLIF file per function. No `; data:` directives: our code references cg_clif's data
//!    objects themselves, so every data object keeps a single identity (addresses of statics,
//!    vtables, `Location`s are the ones cg_clif's code and every other crate see).
//! 3. `lean-backend` compiles each function in its own file, so a call to another function is
//!    a call of an extern (`E2E.backend_correct_final` covers extern calls through its callee
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
use crate::report::{FnReport, Status};
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
            for l in text.lines() {
                if let Some(s) = l.strip_prefix("; symbol ") {
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
                by_symbol.insert(s, Dump { stem: stem.to_string(), instance });
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
}

/// data-export names `.LdataN` of the object `c_LdataN` (the dump directory is `c.clif`).
fn obj_name_of(ours: &str) -> String {
    match ours.strip_prefix("c_Ldata") {
        Some(hex) => format!(".Ldata{hex}"),
        None => ours.to_string(),
    }
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
        })
        .collect()
}

/// Process one CGU object in place. `id` names the CGU uniquely in the build (unit + object).
pub fn process_object(cfg: &Config, index: &DumpIndex, obj: &Path, id: &str) -> CguResult {
    let syms = match read_syms(obj) {
        Ok(s) => s,
        Err(e) => return CguResult { functions: vec![], changed: false, error: Some(e) },
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
            bad = Some(if u.starts_with("alloc") || u.starts_with("data_") || u.starts_with("u0_") {
                // normalize.py's name for a gv/callee no relocation of cg_clif's
                // object names, e.g. data only a path Cranelift's optimiser removed uses
                format!("references `{u}`, which cg_clif's object does not contain (removed by Cranelift's optimiser, or unmapped)")
            } else {
                format!("references `{u}`, unknown to cg_clif's object")
            });
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

/// Compile one function from its normalised `.unopt.clif` dump into `o/f{i}.o`.
///
/// Retry: the unoptimised CLIF may reference data objects that cg_clif's optimiser removed
/// from its object — the unoptimised dump still holds the (dead) panic paths of e.g.
/// `rotate_left`, whose `Location` objects cg_clif's object does not contain when the
/// optimised code dropped them. The optimised dump (`{stem}.opt.clif`, normalised with the
/// same gvmap) matches the code cg_clif actually emitted, so compiling it references only
/// data that exists. Only the "removed by Cranelift's optimiser, or unmapped" references
/// trigger the retry; a failing retry keeps the unopt result (whose reference check then
/// reports the fallback reason).
fn compile_one(
    cfg: &Config,
    syms: &ObjSyms,
    split: &Path,
    outdir: &Path,
    i: usize,
    d: &Dump,
    sym: &str,
) -> Compiled {
    let run_backend = |input: &Path, out: &Path| -> Compiled {
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
            .env("LEAN_REGALLOC", cfg.lean_regalloc());
        // `--keep-temps`: keep lean-regalloc's output next to the object (`cargo fv
        // link-proof` rebuilds the allocation from it in Lean): this process (fv-rustc) runs
        // lean-regalloc and copies its output (`crate::linkproof::regalloc_tee`)
        if cfg.keep_link() {
            if let Ok(me) = std::env::current_exe() {
                cmd.env("LEAN_REGALLOC", me)
                    .env(crate::linkproof::RA_REAL, cfg.lean_regalloc())
                    .env(crate::linkproof::RA_OUT, out.with_extension("ra.json"));
            }
        }
        match cmd.output() {
            Ok(o) => {
                drop(slot);
                classify(cfg, &String::from_utf8_lossy(&o.stderr), o.status.success(), out, sym, input)
            }
            Err(e) => Compiled::Fallback(format!("cannot run lean-backend: {e}")),
        }
    };
    let out = outdir.join(format!("f{i}.o"));
    let c = run_backend(&split.join(format!("{}.unopt.clif", d.stem)), &out);
    if let Compiled::Ok { .. } = &c {
        if let Some(why) = missing_ref(&out, syms) {
            let opt = split.join(format!("{}.opt.clif", d.stem));
            if why.contains("does not contain") && opt.exists() {
                let out_opt = outdir.join(format!("f{i}.opt.o"));
                let c2 = run_backend(&opt, &out_opt);
                if let Compiled::Ok { obj, unverified, normal_returns, clif } = c2 {
                    if missing_ref(&obj, syms).is_none() {
                        return Compiled::Ok { obj, unverified, normal_returns, clif };
                    }
                }
            }
        }
    }
    c
}

/// `all`: every function of the CGU (the normalisation input: data-export and the FuncId
/// naming need the whole CGU); `funcs`: the ones to compile.
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
        return CguResult { functions: vec![], changed: false, error: None };
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
        Ok((functions, changed)) => CguResult { functions, changed, error: None },
        Err(e) => CguResult { functions: fallback_all(&funcs, &e), changed: false, error: Some(e) },
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
/// theorem covers for its normal returns only; `clif`: the file it compiled).
enum Compiled {
    Ok { obj: PathBuf, unverified: Option<String>, normal_returns: bool, clif: PathBuf },
    Fallback(String),
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
    for l in stderr.lines() {
        if l.contains(": compiled, verified for normal returns") {
            normal_returns = true;
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
    if cfg.mode == Mode::Opt {
        let why = "--opt: the Lean mid-end ran unproven simplify rules";
        unverified = Some(match unverified {
            Some(u) => format!("{u}; {why}"),
            None => why.into(),
        });
    }
    Compiled::Ok { obj: out.to_path_buf(), unverified, normal_returns, clif: input.to_path_buf() }
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
    fs::write(&bin, [0u8; 4]).map_err(|e| format!("{}: {e}", bin.display()))?;
    run(Command::new(&cfg.objcopy)
        .args(["-I", "binary", "-O", "elf64-littleaarch64", "--rename-section", ".data=.text,alloc,load,readonly,code,contents", "--strip-all"])
        .arg(&bin)
        .arg(&o))?;
    Ok(o)
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
) -> Result<(Vec<FnReport>, bool), String> {
    let clif = work.join("c.clif");
    fs::create_dir_all(&clif).map_err(|e| format!("{}: {e}", clif.display()))?;
    for d in all {
        for ext in ["unopt.clif", "opt.clif", "vcode"] {
            let src = index.dir.join(format!("{}.{ext}", d.stem));
            if src.exists() {
                std::os::unix::fs::symlink(&src, clif.join(format!("{}.{ext}", d.stem)))
                    .map_err(|e| format!("symlink {}: {e}", src.display()))?;
            }
        }
    }
    // 2. data references → cg_clif's own data symbols. Run for both stages: the optimised
    // dump is the retry input when the unoptimised one references data cg_clif's optimiser
    // removed (see `compile_one`), and its gvs need the same gvmap (the keys are normalized
    // to the dump stem by normalize.py, so one merged table serves both stages).
    let gvmap = work.join("gvmap.tsv");
    let fnmap = work.join("fnmap.tsv");
    for stage in ["unopt", "opt"] {
        let gvm = work.join(format!("gvmap.{stage}.tsv"));
        if stage == "unopt" {
            run(Command::new(cfg.data_export())
                .arg(&clif)
                .arg(obj)
                .arg("--stage")
                .arg(stage)
                .arg("--out")
                .arg(work.join(format!("data-{stage}.clif")))
                .arg("--gvmap")
                .arg(&gvm)
                .arg("--fnmap")
                .arg(&fnmap)
                .arg("--imported"))?;
            fs::copy(&gvm, &gvmap).map_err(|e| format!("{}: {e}", gvm.display()))?;
        } else {
            // Best effort: a failure only disables the missing-data retry (normalize.py
            // keeps only the gvmap entries of its own stage; the unopt run's fnmap stays).
            match run(Command::new(cfg.data_export())
                .arg(&clif)
                .arg(obj)
                .arg("--stage")
                .arg(stage)
                .arg("--out")
                .arg(work.join(format!("data-{stage}.clif")))
                .arg("--gvmap")
                .arg(&gvm)
                .arg("--fnmap")
                .arg(&fnmap)
                .arg("--imported"))
            {
                Ok(_) => {
                    let extra =
                        fs::read_to_string(&gvm).map_err(|e| format!("{}: {e}", gvm.display()))?;
                    let mut f = fs::OpenOptions::new()
                        .append(true)
                        .open(&gvmap)
                        .map_err(|e| format!("{}: {e}", gvmap.display()))?;
                    use std::io::Write;
                    f.write_all(extra.as_bytes()).map_err(|e| format!("{}: {e}", gvmap.display()))?;
                }
                Err(e) => eprintln!("cargo fv: warning: {tag}: no gvmap for .opt.clif ({e})"),
            }
        }
    }
    let split = work.join("split");
    run(Command::new(&cfg.python)
        .arg(cfg.normalize())
        .arg(&clif)
        .arg("unopt")
        .arg(&split)
        .arg("--split")
        .arg("--strip-srcloc")
        .arg("--gvmap")
        .arg(&gvmap)
        .arg("--fnmap")
        .arg(&fnmap))?;
    // The optimised split files: best effort — a failure only disables the
    // missing-data retry (the unopt compilation and its fallback reason are unaffected).
    let split_opt = work.join("split-opt");
    match run(Command::new(&cfg.python)
        .arg(cfg.normalize())
        .arg(&clif)
        .arg("opt")
        .arg(&split_opt)
        .arg("--split")
        .arg("--strip-srcloc")
        .arg("--gvmap")
        .arg(&gvmap)
        .arg("--fnmap")
        .arg(&fnmap))
    {
        Ok(_) => {
            for e in fs::read_dir(&split_opt).map_err(|e| format!("{}: {e}", split_opt.display()))?.flatten() {
                let to = split.join(e.file_name());
                fs::rename(e.path(), &to).map_err(|err| format!("{}: {err}", to.display()))?;
            }
        }
        Err(e) => eprintln!("cargo fv: warning: {tag}: no .opt.clif split ({e})"),
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
    for ((sym, d), c) in funcs.iter().zip(results) {
        let mut report = |status, reason: Option<String>, normal_returns: bool| {
            reports.push(FnReport {
                symbol: sym.clone(),
                instance: d.instance.clone(),
                status,
                reason,
                normal_returns,
            })
        };
        match c {
            Compiled::Fallback(why) => report(Status::Fallback, Some(why), false),
            Compiled::Ok { obj: o, unverified, normal_returns, clif } => {
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
                        bad = Some(format!("unverified ({u}): cg_clif's code kept under --lean-link"));
                    }
                }
                match bad {
                    Some(b) => report(Status::Fallback, Some(b), false),
                    None => {
                        referenced_locals.extend(locals);
                        link_fns.push(serde_json::json!({
                            "symbol": sym,
                            "clif": clif,
                            "ra": o.with_extension("ra.json"),
                            "verified": unverified.is_none(),
                            "reason": unverified,
                        }));
                        ours.push((sym.clone(), o));
                        match unverified {
                            Some(u) => report(Status::Unverified, Some(u), false),
                            None => report(Status::Verified, None, normal_returns),
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

    // our functions: one relocatable object, same renaming (data names too), markers. With
    // `--lean-link` every function is followed by a zero word (the Lean linker's placement,
    // `Link.offs`: the gap word), so that `ld -r` lays the code out as the Lean linker places it.
    let lean = work.join("lean.o");
    let mut inputs: Vec<PathBuf> = Vec::new();
    if cfg.lean_link {
        let pad = gap_object(cfg, work)?;
        for (_, o) in &ours {
            inputs.push(o.clone());
            inputs.push(pad.clone());
        }
    } else {
        inputs.extend(ours.iter().map(|(_, o)| o.clone()));
    }
    run(Command::new(&cfg.rust_lld).args(["-flavor", "gnu", "-r", "-o"]).arg(&lean).args(&inputs))?;
    let lean_syms = read_syms(&lean)?;
    let mut ours_redef: Vec<String> = renames.iter().map(|(a, b)| format!("{a} {b}")).collect();
    // the CLIF names of our code → the final symbol names (`cargo fv link-proof`)
    let mut clif_names: BTreeMap<String, String> =
        ours.iter().map(|(s, _)| (s.clone(), final_name(s))).collect();
    for u in &lean_syms.undefined {
        let n = obj_name_of(u);
        clif_names.insert(u.clone(), final_name(&n));
        if n != *u {
            ours_redef.push(format!("{u} {}", final_name(&n)));
        }
    }
    let ours_redef_path = work.join("redefine-lean.txt");
    write_list(&ours_redef_path, ours_redef)?;
    objcopy(&[format!("--redefine-syms={}", ours_redef_path.display())], &lean)?;
    let lean_syms = read_syms(&lean)?;
    let lean_file_data = fs::read(&lean).map_err(|e| format!("{}: {e}", lean.display()))?;
    let lean_file = object::File::parse(&*lean_file_data).map_err(|e| format!("{}: {e}", lean.display()))?;
    let mut markers = Vec::new();
    for (s, _) in &ours {
        let n = final_name(s);
        let Some(&(si, v)) = lean_syms.at.get(&n) else {
            return Err(format!("internal: `{n}` missing from the merged Lean object"));
        };
        let sec = object::read::ObjectSection::name(
            &object::read::Object::section_by_index(&lean_file, object::SectionIndex(si))
                .map_err(|e| format!("{}: {e}", lean.display()))?,
        )
        .map_err(|e| format!("{}: {e}", lean.display()))?
        .to_string();
        // global here (llvm-objcopy appends added symbols after the globals, so a local one
        // breaks the symbol table order); localised with the renamed symbols after the merge
        markers.push(format!("--add-symbol={MARKER}{n}={sec}:{v},global,function"));
    }
    let rsp = work.join("markers.rsp");
    write_list(&rsp, markers)?;
    run(Command::new(&cfg.objcopy).arg(format!("@{}", rsp.display())).arg(&lean))?;

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
                return Err(format!("internal: after the merge `{n}` does not resolve to the Lean code"));
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
        let j = serde_json::json!({
            "tag": tag,
            "object": obj.file_name().map(|n| n.to_string_lossy().into_owned()),
            "functions": link_fns,
            "names": clif_names,
        });
        let p = work.join(crate::linkproof::CGU_FILE);
        fs::write(&p, serde_json::to_string_pretty(&j).unwrap_or_default())
            .map_err(|e| format!("{}: {e}", p.display()))?;
    }
    Ok((reports, true))
}
