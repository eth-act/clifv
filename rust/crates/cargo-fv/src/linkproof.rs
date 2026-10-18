//! `cargo fv link-proof`: the frontend bundle of an executable's program part
//! (docs/contracts/frontend.md), the input of the Lean-built `LinkSpec` (`Front.buildSpec`,
//! `FV/Front/Bundle.lean`) that `lake exe lean-link` compiles and `lake exe link-check` checks.
//!
//! A build with `--keep-temps` keeps, per codegen unit, cg_clif's dump of every Lean-compiled
//! function (the stage `lean-backend` compiled the decoding of), the register allocator's answers
//! for it (`lean-backend` writes them to `$FV_RA_OUT`), the unit's data objects (`data.clif`), and the merge's record
//! (`fv-link.json`, written by `pipeline::process_in`: the names the merge gave the symbols it
//! renamed, the object's local symbols); per linked executable, the lld link map
//! (`link-<tag>.map`, `link-<tag>.json`). This command only collects them, unchanged, into
//! `DIR/bundle.json`: per unit its tag, the paths of the function dumps and regalloc files, the
//! path of its data objects, its local symbols and their link-map addresses, the merge's names;
//! the executable's symbols (those defined once); the address of each function's Lean code (its
//! `__fvlean$` marker); the functions it cannot include (unverified, or no unique marker). No
//! CLIF or data text is rewritten here: the decoding of the dumps, the renaming to linked names,
//! the data closure and the CLIF image's symbols are computed in Lean (`Front.assemble`), with
//! proofs (`FV/Front/BundleProof.lean`, `FV/Front/RawProof.lean`).
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::pipeline::MARKER;

/// Where `lean-backend` keeps its register-allocation answers (set by `pipeline::compile_one`
/// with `--keep-temps`; the schema of `lean-regalloc`'s output, docs/contracts/regalloc.md).
pub const RA_OUT: &str = "FV_RA_OUT";
/// The per-codegen-unit record in its work directory.
pub const CGU_FILE: &str = "fv-link.json";

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


struct Opts {
    exe: Vec<String>,
    krate: Option<String>,
    out: PathBuf,
    lean: Option<PathBuf>,
    module: Option<String>,
    entries: Option<String>,
    prune: bool,
    mode: String,
    /// `--cgus FILE`: the codegen units' work directories, in this order (the Lean linker's
    /// placement order), instead of the units the link map names
    cgus: Option<PathBuf>,
    /// `--no-check`: write the directory only (no `link-check`)
    no_check: bool,
}

const LP_USAGE: &str = "\
usage: cargo fv link-proof [--exe SUBSTR]… [--crate NAME] [--out DIR] [--lean FILE.lean --module NAME]
                           [--entries a,b,…] [--prune] [--mode DIR] [--manifest-path PATH]
                           [--cgus FILE] [--no-check]

After `cargo fv build|test --keep-temps`: the Lean-compiled, verified functions of the executable
whose path contains every SUBSTR (default: the only one), restricted to the codegen units of the crate
NAME (its units `NAME-<hash>`), as the input of the crate-level linking theorem
(docs/contracts/e2e.md, \"Crate-level instance\"): DIR (default target/fv/link-proof) gets
bundle.json, the frontend bundle (docs/contracts/frontend.md) from which Lean builds the program
(names, data closure). Then `lake exe link-check DIR` reports
which premises of LinkSys.Ok fail (per function), and with --lean writes the Lean file proving
LinkSys.Ok by native_decide and the theorem for the entries (default: every function); put it in
the repository's crate-proofs/Crates/ and build it there with `lake build Crates.NAME` (the checker
then runs as compiled code). --prune drops the failing functions until the rest passes. --mode:
the build's directory under target/fv (default plain). --cgus FILE: the codegen units' work
directories, one per line, in this order (the Lean linker's placement order, `--lean-link`)
instead of those the link map names; --no-check: write DIR only.";

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
        cgus: None,
        no_check: false,
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
            "--cgus" => o.cgus = Some(PathBuf::from(val()?)),
            "--no-check" => o.no_check = true,
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
    let dirs: Vec<PathBuf> = match &o.cgus {
        Some(f) => fs::read_to_string(f)
            .map_err(|e| format!("{}: {e}", f.display()))?
            .lines()
            .filter(|l| !l.is_empty())
            .map(PathBuf::from)
            .collect(),
        None => fs::read_dir(&tmp).map_err(|e| format!("{}: {e}", tmp.display()))?.flatten().map(|e| e.path()).collect(),
    };
    for d in dirs {
        let p = d.join(CGU_FILE);
        if !p.exists() {
            continue;
        }
        let j = read_json(&p)?;
        let obj = j["object"].as_str().unwrap_or_default().to_string();
        if o.cgus.is_none() && !map.objects.contains(&obj) {
            continue;
        }
        if let Some(k) = &o.krate {
            if !obj.starts_with(&format!("{k}-")) {
                continue;
            }
        }
        cgu_dir.insert(obj.clone(), d);
        cgus.push((obj, j));
    }
    if o.cgus.is_none() {
        cgus.sort_by(|a, b| a.0.cmp(&b.0));
    }
    if cgus.is_empty() {
        return Err(format!("no Lean-compiled codegen unit of {exe}{} was kept", o.krate.as_deref().map(|k| format!(" of crate {k}")).unwrap_or_default()));
    }
    let _ = fs::remove_dir_all(&o.out);
    fs::create_dir_all(&o.out).map_err(|e| format!("{}: {e}", o.out.display()))?;
    let mut units = Vec::new();
    let mut markers: BTreeMap<String, u64> = BTreeMap::new();
    let mut skipped: Vec<(String, String)> = Vec::new();
    let mut nfuncs = 0;
    for (obj, j) in &cgus {
        let dir = &cgu_dir[obj];
        let rec = dir.join(CGU_FILE);
        let tag = dir.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        let mut functions = Vec::new();
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
            let dump = PathBuf::from(f["dump"].as_str().unwrap_or_default());
            let ra = PathBuf::from(f["ra"].as_str().unwrap_or_default());
            for p in [&dump, &ra] {
                if !p.is_file() {
                    return Err(format!("{}: missing (rebuild with --keep-temps)", p.display()));
                }
            }
            markers.insert(fin.clone(), addr);
            functions.push(serde_json::json!({
                "name": f["symbol"],
                "final": fin,
                "dump": dump,
                "ra": ra,
            }));
        }
        nfuncs += functions.len();
        let Some(locals) = j["locals"].as_array() else {
            return Err(format!("{}: no `locals` (written by an older cargo fv: rebuild)", rec.display()));
        };
        let locals: Vec<(String, String)> = locals
            .iter()
            .filter_map(|p| Some((p[0].as_str()?.to_string(), p[1].as_str()?.to_string())))
            .collect();
        // the link map's address of each local symbol of the unit's object (defined once there)
        let local_addrs: Vec<(String, u64)> = locals
            .iter()
            .filter_map(|(_, s)| {
                let a = map.local.get(&(obj.clone(), s.clone())).filter(|a| a.len() == 1)?;
                Some((s.clone(), *a.iter().next()?))
            })
            .collect();
        let data = dir.join("data.clif");
        if !data.is_file() {
            return Err(format!("{}: missing (the unit's data objects)", data.display()));
        }
        units.push(serde_json::json!({
            "tag": tag,
            "object": obj,
            "functions": functions,
            "data": data,
            "locals": locals,
            "names": j["names"],
            "local_addrs": local_addrs,
        }));
    }
    // the executable's symbols defined once (the map shows demangled names)
    let exe_syms = read_exe_syms(Path::new(&exe))?;
    let symbols: BTreeMap<&String, u64> = exe_syms
        .iter()
        .filter_map(|(n, a)| if a.len() == 1 { a.iter().next().map(|a| (n, *a)) } else { None })
        .collect();
    let bundle = serde_json::json!({
        "format": "clifv-frontend-bundle",
        "version": 2,
        "exe": exe,
        "map": map_path,
        "units": units,
        "symbols": symbols.iter().map(|(n, a)| serde_json::json!([n, a])).collect::<Vec<_>>(),
        "markers": markers.iter().map(|(n, a)| serde_json::json!([n, a])).collect::<Vec<_>>(),
        "skipped": skipped,
    });
    let bp = o.out.join("bundle.json");
    fs::write(&bp, serde_json::to_string_pretty(&bundle).unwrap_or_default())
        .map_err(|e| format!("{}: {e}", bp.display()))?;
    eprintln!(
        "cargo fv link-proof: {nfuncs} functions of {} codegen unit(s) of {exe} (skipped {}), {} executable symbols → {}",
        cgus.len(),
        skipped.len(),
        symbols.len(),
        bp.display()
    );
    if o.no_check {
        return Ok(0);
    }
    // the checker (and the Lean file)
    let checker = root.join(".lake/build/bin/link-check");
    if !checker.exists() {
        eprintln!("cargo fv link-proof: {} missing (lake build link-check); run it on {}", checker.display(), o.out.display());
        return Ok(0);
    }
    let mut cmd = Command::new(&checker);
    cmd.arg(&o.out).arg("--dead-cleanup");
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
