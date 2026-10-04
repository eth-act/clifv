//! `cargo fv link-proof`: the input of a crate-level instance of the linking theorem
//! (`E2E.backend_correct_program`, `FV/E2E/LinkCheck.lean`; docs/contracts/e2e.md,
//! "Crate-level instance").
//!
//! A build with `--keep-temps` keeps, per codegen unit, the CLIF file `lean-backend` compiled
//! for every Lean-compiled function, `lean-regalloc`'s output for it (`regalloc_tee`), and the
//! names the merge gave its symbols (`fv-link.json`, written by `pipeline::process_in`); per
//! linked executable, the lld link map (`link-<tag>.map`, `link-<tag>.json`). From those this
//! command writes a directory for `lake exe link-check`:
//!
//! * `fns/<i>.clif`: the compiled CLIF with every name replaced by the symbol it is linked as
//!   (local symbols renamed by the merge, `c_LdataN` → the data symbol); `fns/<i>.ra.json`;
//! * `link.json`: the functions; the data objects they reach (`data`: `clif-data-export`'s
//!   `; data:` lines, renamed likewise; an object the merge left local, the assembler's
//!   `.LdataN`, is named `.LdataN@<unit tag>` and found in the link map under its object file);
//!   and the link map's address of every function (its Lean code: the `__fvlean$` marker) and
//!   of every name the functions and data objects refer to.
//!
//! `link-check` then evaluates the checker `E2E.LinkCheck.okB` and the binary checks of
//! `E2E.BinCheck` (the executable's code, data objects and symbol table against the program) on
//! it and (with `--lean`) writes the Lean file that proves `LinkSys.Ok` and `BinOk` for the crate
//! by `native_decide`.
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::ffi::OsString;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::pipeline::MARKER;

/// The real `lean-regalloc` (set by `pipeline::compile_one` with `--keep-temps`).
pub const RA_REAL: &str = "FV_RA_REAL";
/// Where to keep its output.
pub const RA_OUT: &str = "FV_RA_OUT";
/// The per-codegen-unit record in its work directory.
pub const CGU_FILE: &str = "fv-link.json";

/// `fv-rustc` as `lean-regalloc`: run the real one on the same arguments, keep a copy of its
/// standard output in `$FV_RA_OUT`, and pass its output and status through.
pub fn regalloc_tee(real: &str, argv: Vec<OsString>) -> i32 {
    match Command::new(real).args(&argv).output() {
        Ok(o) => {
            if let Some(p) = std::env::var_os(RA_OUT) {
                if let Err(e) = fs::write(&p, &o.stdout) {
                    eprintln!("fv-rustc: {}: {e}", Path::new(&p).display());
                }
            }
            let _ = std::io::stdout().write_all(&o.stdout);
            let _ = std::io::stderr().write_all(&o.stderr);
            o.status.code().unwrap_or(1)
        }
        Err(e) => {
            eprintln!("fv-rustc: cannot run {real}: {e}");
            2
        }
    }
}

/// One line of an lld link map: address and the (indented) text.
enum MapLine {
    Section,
    Input(String),
    Symbol(String, u64),
}

fn parse_map_line(l: &str) -> Option<MapLine> {
    // lld: "%16llx %16llx %8llx %5lld " then the output section, an input (8 spaces deeper) or
    // a symbol (16 spaces deeper)
    if l.len() < 49 || !l.is_char_boundary(49) {
        return None;
    }
    let vma = u64::from_str_radix(l[..16].trim(), 16).ok()?;
    let rest = &l[49..];
    let ind = rest.len() - rest.trim_start().len();
    let text = rest.trim().to_string();
    Some(match ind {
        0 => MapLine::Section,
        8 => MapLine::Input(text),
        _ => MapLine::Symbol(text, vma),
    })
}

/// The object file name of a map input (`/p/x.o:(.text)`, `/p/libx.rlib(m.o):(.text)`).
fn input_object(text: &str) -> String {
    let t = text.rsplit_once(":(").map(|(a, _)| a).unwrap_or(text);
    if let Some(inner) = t.strip_suffix(')').and_then(|t| t.rsplit_once('(').map(|(_, m)| m)) {
        return inner.to_string();
    }
    Path::new(t).file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default()
}

struct LinkMap {
    /// symbol → its addresses (a local name may occur in several objects)
    syms: HashMap<String, BTreeSet<u64>>,
    /// (object file name, symbol) → its addresses
    local: HashMap<(String, String), BTreeSet<u64>>,
    /// the object file names linked
    objects: BTreeSet<String>,
}

fn read_map(p: &Path) -> Result<LinkMap, String> {
    let text = fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))?;
    let mut m = LinkMap { syms: HashMap::new(), local: HashMap::new(), objects: BTreeSet::new() };
    let mut cur = String::new();
    for l in text.lines() {
        match parse_map_line(l) {
            Some(MapLine::Input(t)) => {
                cur = input_object(&t);
                m.objects.insert(cur.clone());
            }
            Some(MapLine::Symbol(s, a)) => {
                m.local.entry((cur.clone(), s.clone())).or_default().insert(a);
                m.syms.entry(s).or_default().insert(a);
            }
            _ => {}
        }
    }
    Ok(m)
}

/// The CLIF name of a data object the merge left local (`c_LdataN`, the assembler's `.LdataN`,
/// which repeats across codegen units) as its symbol `.LdataN` qualified by the unit's tag:
/// `.LdataN@<tag>` (the binary checks look up `.LdataN` in the executable's symbol table).
fn local_data_name(clif: &str, tag: &str) -> Option<String> {
    clif.strip_prefix("c_").filter(|n| n.starts_with("Ldata")).map(|n| format!(".{n}@{tag}"))
}
/// The data objects of a codegen unit (`clif-data-export`'s `; data: %name [writable] = …`
/// lines) with the names their contents refer to.
fn read_data_refs(p: &Path) -> HashMap<String, Vec<String>> {
    let mut m = HashMap::new();
    for l in fs::read_to_string(p).unwrap_or_default().lines() {
        let Some(rest) = l.strip_prefix("; data: %") else { continue };
        let name: String = rest.chars().take_while(|c| is_name_char(*c)).collect();
        let refs = rest
            .split_once(" = ")
            .map(|(_, items)| {
                items
                    .split_whitespace()
                    .filter_map(|t| t.strip_prefix('%'))
                    .map(|t| t.chars().take_while(|c| is_name_char(*c)).collect::<String>())
                    .collect()
            })
            .unwrap_or_default();
        m.insert(name, refs);
    }
    m
}

/// The `; data:` lines of a codegen unit's data objects, by object name.
fn read_data_lines(p: &Path) -> HashMap<String, String> {
    let mut m = HashMap::new();
    for l in fs::read_to_string(p).unwrap_or_default().lines() {
        let Some(rest) = l.strip_prefix("; data: %") else { continue };
        let name: String = rest.chars().take_while(|c| is_name_char(*c)).collect();
        m.insert(name, l.to_string());
    }
    m
}

/// The defined symbols of an executable: name → addresses.
fn read_exe_syms(p: &Path) -> Result<HashMap<String, BTreeSet<u64>>, String> {
    use object::{Object, ObjectSymbol, SymbolKind};
    let data = fs::read(p).map_err(|e| format!("{}: {e}", p.display()))?;
    let file = object::File::parse(&*data).map_err(|e| format!("{}: {e}", p.display()))?;
    let mut m: HashMap<String, BTreeSet<u64>> = HashMap::new();
    for s in file.symbols() {
        let Ok(n) = s.name() else { continue };
        if n.is_empty() || s.is_undefined() || matches!(s.kind(), SymbolKind::Section | SymbolKind::File) {
            continue;
        }
        m.entry(n.to_string()).or_default().insert(s.address());
    }
    Ok(m)
}


fn is_name_char(c: char) -> bool {
    c.is_ascii_alphanumeric() || c == '_' || c == '.' || c == '$'
}

/// `text` with every `%name` renamed by `names`; also returns the names (after renaming).
fn rename_clif(text: &str, names: &BTreeMap<String, String>) -> (String, BTreeSet<String>) {
    let mut out = String::with_capacity(text.len() + 256);
    let mut seen = BTreeSet::new();
    let mut it = text.char_indices().peekable();
    while let Some((i, c)) = it.next() {
        out.push(c);
        if c != '%' {
            continue;
        }
        let mut end = i + 1;
        while let Some(&(j, d)) = it.peek() {
            if !is_name_char(d) {
                break;
            }
            end = j + d.len_utf8();
            it.next();
        }
        let n = &text[i + 1..end];
        let r = names.get(n).cloned().unwrap_or_else(|| n.to_string());
        if !r.is_empty() {
            seen.insert(r.clone());
        }
        out.push_str(&r);
    }
    (out, seen)
}

struct Opts {
    exe: Vec<String>,
    krate: Option<String>,
    out: PathBuf,
    lean: Option<PathBuf>,
    module: Option<String>,
    entries: Option<String>,
    prune: bool,
    mode: String,
}

const LP_USAGE: &str = "\
usage: cargo fv link-proof [--exe SUBSTR]… [--crate NAME] [--out DIR] [--lean FILE.lean --module NAME]
                           [--entries a,b,…] [--prune] [--mode DIR] [--manifest-path PATH]

After `cargo fv build|test --keep-temps`: the Lean-compiled, verified functions of the executable
whose path contains every SUBSTR (default: the only one), restricted to the codegen units of the crate
NAME (its units `NAME-<hash>`), as the input of the crate-level linking theorem
(docs/contracts/e2e.md, \"Crate-level instance\"): DIR (default target/fv/link-proof) gets the
renamed CLIF files, the regalloc outputs and link.json. Then `lake exe link-check DIR` reports
which premises of LinkSys.Ok fail (per function), and with --lean writes the Lean file proving
LinkSys.Ok by native_decide and the theorem for the entries (default: every function); put it in
the repository's crate-proofs/Crates/ and build it there with `lake build Crates.NAME` (the checker
then runs as compiled code). --prune drops the failing functions until the rest passes. --mode:
the build's directory under target/fv (default plain).";

fn parse_opts(args: &[String], target: &Path) -> Result<Opts, String> {
    let mut o = Opts {
        exe: Vec::new(),
        krate: None,
        out: target.join("fv/link-proof"),
        lean: None,
        module: None,
        entries: None,
        prune: false,
        mode: "plain".into(),
    };
    let mut it = args.iter();
    while let Some(a) = it.next() {
        let mut val = || it.next().cloned().ok_or_else(|| format!("{a}: missing value\n{LP_USAGE}"));
        match a.as_str() {
            "--exe" => o.exe.push(val()?),
            "--crate" => o.krate = Some(val()?),
            "--out" => o.out = PathBuf::from(val()?),
            "--lean" => o.lean = Some(PathBuf::from(val()?)),
            "--module" => o.module = Some(val()?),
            "--entries" => o.entries = Some(val()?),
            "--mode" => o.mode = val()?,
            "--manifest-path" => {
                val()?;
            }
            "--prune" => o.prune = true,
            "-h" | "--help" => return Err(LP_USAGE.into()),
            _ => return Err(format!("unknown option {a}\n{LP_USAGE}")),
        }
    }
    Ok(o)
}

fn read_json(p: &Path) -> Result<serde_json::Value, String> {
    let t = fs::read_to_string(p).map_err(|e| format!("{}: {e}", p.display()))?;
    serde_json::from_str(&t).map_err(|e| format!("{}: {e}", p.display()))
}

/// `cargo fv link-proof`; `target`: cargo's target directory, `root`: the repository.
pub fn run(target: &Path, root: &Path, args: &[String]) -> Result<i32, String> {
    let o = parse_opts(args, target)?;
    let tmp = target.join("fv").join(&o.mode).join("tmp");
    // the executable
    let mut links = Vec::new();
    for e in fs::read_dir(&tmp).map_err(|e| format!("{}: {e} (build with --keep-temps)", tmp.display()))?.flatten() {
        let n = e.file_name().to_string_lossy().into_owned();
        if n.starts_with("link-") && n.ends_with(".json") {
            let j = read_json(&e.path())?;
            let out = j["output"].as_str().unwrap_or_default().to_string();
            if o.exe.iter().all(|s| out.contains(s.as_str())) {
                links.push((out, PathBuf::from(j["map"].as_str().unwrap_or_default())));
            }
        }
    }
    let (exe, map_path) = match links.len() {
        1 => links.remove(0),
        0 => return Err(format!("no linked executable{} in {} (build with --keep-temps)",
            if o.exe.is_empty() { String::new() } else { format!(" matching {:?}", o.exe) }, tmp.display())),
        _ => return Err(format!("several executables; choose one with --exe:\n  {}",
            links.iter().map(|l| l.0.as_str()).collect::<Vec<_>>().join("\n  "))),
    };
    let map = read_map(&map_path)?;
    // the codegen units linked into it
    let mut cgus = Vec::new();
    let mut cgu_dir: HashMap<String, PathBuf> = HashMap::new();
    for e in fs::read_dir(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?.flatten() {
        let p = e.path().join(CGU_FILE);
        if !p.exists() {
            continue;
        }
        let j = read_json(&p)?;
        let obj = j["object"].as_str().unwrap_or_default().to_string();
        if !map.objects.contains(&obj) {
            continue;
        }
        if let Some(k) = &o.krate {
            if !obj.starts_with(&format!("{k}-")) {
                continue;
            }
        }
        cgu_dir.insert(obj.clone(), e.path());
        cgus.push((obj, j));
    }
    cgus.sort_by(|a, b| a.0.cmp(&b.0));
    if cgus.is_empty() {
        return Err(format!("no Lean-compiled codegen unit of {exe}{} was kept", o.krate.as_deref().map(|k| format!(" of crate {k}")).unwrap_or_default()));
    }
    let _ = fs::remove_dir_all(&o.out);
    let fns_dir = o.out.join("fns");
    fs::create_dir_all(&fns_dir).map_err(|e| format!("{}: {e}", fns_dir.display()))?;
    let mut funcs = Vec::new();
    let mut referenced: BTreeSet<String> = BTreeSet::new();
    let mut fn_addr: BTreeMap<String, u64> = BTreeMap::new();
    let mut skipped: Vec<(String, String)> = Vec::new();
    // functions whose address is in a data object the functions reach (vtables): CLIF image
    // symbols, so that an indirect call through them resolves
    let mut data_fns: BTreeSet<String> = BTreeSet::new();
    // the reachable data objects (`; data:` lines renamed to the linked symbols; the binary
    // checks compare them with the executable's bytes)
    let mut data_lines: Vec<String> = Vec::new();
    // the addresses of the data objects the merge left local (`local_data_name`)
    let mut local_addr: BTreeMap<String, u64> = BTreeMap::new();
    for (obj, j) in &cgus {
        let unopt = cgu_dir.get(obj).map(|d| d.join("data-unopt.clif"));
        let data = unopt.as_deref().map(read_data_refs).unwrap_or_default();
        let lines = unopt.as_deref().map(read_data_lines).unwrap_or_default();
        let mut start: Vec<String> = Vec::new();
        let mut names: BTreeMap<String, String> = j["names"]
            .as_object()
            .map(|m| m.iter().filter_map(|(k, v)| v.as_str().map(|v| (k.clone(), v.to_string()))).collect())
            .unwrap_or_default();
        // a renamed function's self-call alias `f__fvself` (`link-check` pairs it with `f` by
        // name) is renamed with it
        let aliases: Vec<(String, String)> =
            names.iter().map(|(k, v)| (format!("{k}__fvself"), format!("{v}__fvself"))).collect();
        for (k, v) in aliases {
            names.entry(k).or_insert(v);
        }
        for f in j["functions"].as_array().into_iter().flatten() {
            let fin = f["final"].as_str().unwrap_or_default().to_string();
            if !f["verified"].as_bool().unwrap_or(false) {
                skipped.push((fin, format!("unverified: {}", f["reason"].as_str().unwrap_or("?"))));
                continue;
            }
            let addrs = map.syms.get(&format!("{MARKER}{fin}"));
            let Some(&addr) = addrs.filter(|a| a.len() == 1).and_then(|a| a.iter().next()) else {
                skipped.push((fin, "no unique Lean code address in the link map (removed by --gc-sections?)".into()));
                continue;
            };
            let clif = PathBuf::from(f["clif"].as_str().unwrap_or_default());
            let ra = PathBuf::from(f["ra"].as_str().unwrap_or_default());
            let text = fs::read_to_string(&clif).map_err(|e| format!("{}: {e}", clif.display()))?;
            let (renamed, seen) = rename_clif(&text, &names);
            start.extend(rename_clif(&text, &BTreeMap::new()).1);
            let i = funcs.len();
            let cp = fns_dir.join(format!("{i}.clif"));
            let rp = fns_dir.join(format!("{i}.ra.json"));
            fs::write(&cp, renamed).map_err(|e| format!("{}: {e}", cp.display()))?;
            fs::copy(&ra, &rp).map_err(|e| format!("{}: {e} (rebuild with --keep-temps)", ra.display()))?;
            referenced.extend(seen);
            fn_addr.insert(fin.clone(), addr);
            funcs.push(serde_json::json!({
                "name": fin,
                "clif": format!("fns/{i}.clif"),
                "ra": format!("fns/{i}.ra.json"),
                "object": obj,
                "symbol": f["symbol"],
            }));
        }
        // the data objects reachable from the functions' names, and the functions they hold
        let tag = cgu_dir.get(obj).and_then(|d| d.file_name()).map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        let mut dnames = names.clone();
        for d in data.keys() {
            if dnames.contains_key(d) {
                continue;
            }
            if let Some(l) = local_data_name(d, &tag) {
                let sym = l.split('@').next().unwrap_or_default().to_string();
                if let Some(a) = map.local.get(&(obj.clone(), sym)).filter(|a| a.len() == 1).and_then(|a| a.iter().next()) {
                    local_addr.insert(l.clone(), *a);
                }
                dnames.insert(d.clone(), l);
            }
        }
        let mut seen: BTreeSet<String> = BTreeSet::new();
        let mut todo: Vec<String> = start.into_iter().filter(|n| data.contains_key(n)).collect();
        while let Some(d) = todo.pop() {
            if !seen.insert(d.clone()) {
                continue;
            }
            if let Some(l) = lines.get(&d) {
                let (renamed, names_in) = rename_clif(l, &dnames);
                data_lines.push(renamed);
                referenced.extend(names_in);
            }
            for r in data.get(&d).into_iter().flatten() {
                if data.contains_key(r) {
                    todo.push(r.clone());
                } else {
                    data_fns.insert(names.get(r).cloned().unwrap_or_else(|| r.clone()));
                }
            }
        }
    }
    let data_fns: Vec<&String> = data_fns.iter().filter(|n| fn_addr.contains_key(*n)).collect();
    // the addresses: functions at their Lean code (the map's markers), other names where the
    // executable's symbol table has them (the map shows demangled names)
    let exe_syms = read_exe_syms(Path::new(&exe))?;
    let mut addrs: Vec<(String, u64)> = fn_addr.iter().map(|(n, a)| (n.clone(), *a)).collect();
    let mut unresolved = Vec::new();
    for n in &referenced {
        if fn_addr.contains_key(n) {
            continue;
        }
        if let Some(a) = local_addr.get(n) {
            addrs.push((n.clone(), *a));
            continue;
        }
        match exe_syms.get(n) {
            Some(a) if a.len() == 1 => addrs.push((n.clone(), *a.iter().next().unwrap_or(&0))),
            Some(a) => unresolved.push(format!("{n} (defined {} times)", a.len())),
            None => unresolved.push(n.clone()),
        }
    }
    let link = serde_json::json!({
        "exe": exe,
        "map": map_path,
        "functions": funcs,
        "addrs": addrs,
        "unresolved": unresolved,
        "data_syms": data_fns,
        "data": data_lines,
        "skipped": skipped,
    });
    let lp = o.out.join("link.json");
    fs::write(&lp, serde_json::to_string_pretty(&link).unwrap_or_default()).map_err(|e| format!("{}: {e}", lp.display()))?;
    eprintln!(
        "cargo fv link-proof: {} functions of {} codegen unit(s) of {exe} (skipped {}), {} addresses ({} names unresolved) → {}",
        funcs.len(),
        cgus.len(),
        skipped.len(),
        addrs.len(),
        unresolved.len(),
        o.out.display()
    );
    // the checker (and the Lean file)
    let checker = root.join(".lake/build/bin/link-check");
    if !checker.exists() {
        eprintln!("cargo fv link-proof: {} missing (lake build link-check); run it on {}", checker.display(), o.out.display());
        return Ok(0);
    }
    let mut cmd = Command::new(&checker);
    cmd.arg(&o.out);
    if let Some(l) = &o.lean {
        cmd.arg("--lean").arg(l);
    }
    if let Some(m) = &o.module {
        cmd.arg("--module").arg(m);
    }
    if let Some(e) = &o.entries {
        cmd.arg("--entries").arg(e);
    }
    if o.prune {
        cmd.arg("--prune");
    }
    let st = cmd.status().map_err(|e| format!("{}: {e}", checker.display()))?;
    Ok(st.code().unwrap_or(1))
}
