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
//!
//! The codegen units: with `--lean-link`, those whose Lean code is in the executable's region,
//! the list `lean-link`'s input was built from (the link record's `cgus`), whether or not the
//! link took the unit's own object: rust-lld and lean-ld leave an archive member out when the
//! region object defines every symbol the program needs from it, and the unit's functions are
//! still in the region (#1130). Without `--lean-link`, the units whose object the link map names
//! (the Lean code is inside that object). Every Lean-compiled function of the executable (its
//! `__fvlean$` marker is in the link map) that is not in the bundle is named
//! ([`NOT_IN_BUNDLE`]): the binary check does not cover it.
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
/// The text of `link-proof`'s line naming the Lean-compiled functions of the executable that
/// are not in the bundle (`cargo fv link-proof: <exe>: N Lean-compiled function(s) of the
/// executable … <NOT_IN_BUNDLE>: <object> (n), …`); the binary check's verdict reads it.
pub const NOT_IN_BUNDLE: &str = "are not in the bundle, so the binary check does not cover them";

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
the build's directory under target/fv (default plain). The codegen units: with --lean-link those
of the executable's region (the list lean-link's input was built from, also units whose own
object the link did not take), else those whose object the link map names; --cgus FILE: the
codegen units' work directories, one per line, in this order instead; --no-check: write DIR
only. A Lean-compiled function of the executable that is not in the bundle is named.";

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

/// Where `ld -r` starts a unit's region functions `fns` (final name, `.text` alignment, in
/// placement order), as the Lean linker's placement takes it (`Link.LinkSpec.aligns`,
/// `Link.offsA`; #1061): the unit's `lean.o` is one `.text` of its functions' largest alignment,
/// so its first function starts at that alignment, every other one at its own. Only the
/// functions beyond a word are listed (`Front.Bundle.aligns`).
fn region_aligns(fns: &[(String, u64)]) -> Vec<(String, u64)> {
    let unit = fns.iter().map(|(_, a)| *a).max().unwrap_or(4);
    fns.iter()
        .enumerate()
        .map(|(k, (n, a))| (n.clone(), if k == 0 { unit.max(*a) } else { *a }))
        .filter(|(_, a)| *a > 4)
        .collect()
}

/// The Lean-compiled functions of the executable that are not in the bundle (#1130): the names
/// of the markers (`__fvlean$<name>`) among the link map's symbols `map_syms`, other than the
/// bundle's functions `bundle` and those it lists as skipped (`skipped`), sorted.
fn not_in_bundle<'a>(
    map_syms: impl Iterator<Item = &'a str>,
    bundle: &BTreeMap<String, u64>,
    skipped: &BTreeSet<&str>,
) -> Vec<&'a str> {
    let mut v: Vec<&str> =
        map_syms.filter_map(|s| s.strip_prefix(MARKER)).filter(|f| !bundle.contains_key(*f) && !skipped.contains(f)).collect();
    v.sort_unstable();
    v.dedup();
    v
}

/// The codegen units (object names) of the functions `names` among the work directories in
/// `tmp`, with their counts; `None`: no kept unit has the function.
fn units_of(tmp: &Path, names: &[&str]) -> BTreeMap<Option<String>, usize> {
    let want: BTreeSet<&str> = names.iter().copied().collect();
    let mut unit: HashMap<String, String> = HashMap::new();
    for e in fs::read_dir(tmp).into_iter().flatten().flatten() {
        let Ok(j) = read_json(&e.path().join(CGU_FILE)) else { continue };
        let obj = j["object"].as_str().unwrap_or_default();
        for f in j["functions"].as_array().into_iter().flatten() {
            if let Some(fin) = f["final"].as_str().filter(|n| want.contains(n)) {
                unit.insert(fin.to_string(), obj.to_string());
            }
        }
    }
    let mut by: BTreeMap<Option<String>, usize> = BTreeMap::new();
    for n in names {
        *by.entry(unit.get(*n).cloned()).or_default() += 1;
    }
    by
}

/// The codegen units of the bundle, `(object name, its record, work directory)`: those the list
/// `list` names, in its order (`--cgus FILE`, or with `--lean-link` the region's list the link
/// record names: every unit whose Lean code `lean-link` placed, also when the link did not take
/// the unit's own object, #1130); without a list, those of the work directories in `tmp` whose
/// object the link map names (`objects`), by object name. Only crate `krate`'s units when given.
fn select_units(
    tmp: &Path,
    list: Option<&Path>,
    objects: &BTreeSet<String>,
    krate: Option<&str>,
) -> Result<Vec<(String, serde_json::Value, PathBuf)>, String> {
    let dirs: Vec<PathBuf> = match list {
        Some(f) => fs::read_to_string(f)
            .map_err(|e| format!("{}: {e}", f.display()))?
            .lines()
            .filter(|l| !l.is_empty())
            .map(PathBuf::from)
            .collect(),
        None => fs::read_dir(tmp).map_err(|e| format!("{}: {e}", tmp.display()))?.flatten().map(|e| e.path()).collect(),
    };
    let mut cgus = Vec::new();
    for d in dirs {
        let p = d.join(CGU_FILE);
        if !p.exists() {
            continue;
        }
        let j = read_json(&p)?;
        let obj = j["object"].as_str().unwrap_or_default().to_string();
        if list.is_none() && !objects.contains(&obj) {
            continue;
        }
        if krate.is_some_and(|k| !obj.starts_with(&format!("{k}-"))) {
            continue;
        }
        cgus.push((obj, j, d));
    }
    if list.is_none() {
        cgus.sort_by(|a, b| a.0.cmp(&b.0));
    }
    Ok(cgus)
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
                let list = j["cgus"].as_str().map(PathBuf::from);
                links.push((out, PathBuf::from(j["map"].as_str().unwrap_or_default()), list));
            }
        }
    }
    let (exe, map_path, region_list) = match links.len() {
        1 => links.remove(0),
        0 => return Err(format!("no linked executable{} in {} (build with --keep-temps)",
            if o.exe.is_empty() { String::new() } else { format!(" matching {:?}", o.exe) }, tmp.display())),
        _ => return Err(format!("several executables; choose one with --exe:\n  {}",
            links.iter().map(|l| l.0.as_str()).collect::<Vec<_>>().join("\n  "))),
    };
    let map = read_map(&map_path)?;
    // `--lean-link --verified` (T3c): the functions the link left out of the region (cg_clif's
    // code, outside the program)
    let excluded = crate::leanlink::read_exclude(&tmp, &exe);
    let mut n_excluded = 0;
    let list = o.cgus.clone().or(region_list);
    let cgus = select_units(&tmp, list.as_deref(), &map.objects, o.krate.as_deref())?;
    if cgus.is_empty() {
        return Err(format!("no Lean-compiled codegen unit of {exe}{} was kept", o.krate.as_deref().map(|k| format!(" of crate {k}")).unwrap_or_default()));
    }
    let _ = fs::remove_dir_all(&o.out);
    fs::create_dir_all(&o.out).map_err(|e| format!("{}: {e}", o.out.display()))?;
    let mut units = Vec::new();
    let mut markers: BTreeMap<String, u64> = BTreeMap::new();
    // the region functions `ld -r` starts beyond a word (`Link.LinkSpec.aligns`, #1061)
    let mut aligns: Vec<(String, u64)> = Vec::new();
    let mut skipped: Vec<(String, String)> = Vec::new();
    let mut nfuncs = 0;
    for (obj, j, dir) in &cgus {
        let rec = dir.join(CGU_FILE);
        let tag = dir.file_name().map(|n| n.to_string_lossy().into_owned()).unwrap_or_default();
        let mut functions = Vec::new();
        // the unit's region functions in placement order: (final name, `.text` alignment)
        let mut placed: Vec<(String, u64)> = Vec::new();
        for f in j["functions"].as_array().into_iter().flatten() {
            let fin = f["final"].as_str().unwrap_or_default().to_string();
            if excluded.contains(&fin) {
                n_excluded += 1;
                continue;
            }
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
            // `lean-backend`'s alignment of the function (an older record: a word)
            let align = f["align"].as_u64().unwrap_or(4);
            if align > 4 && addr % align != 0 {
                return Err(format!(
                    "{fin}: its Lean code at {addr:#x} in {exe} is not {align}-aligned (its object's `.text` alignment, #1061)"
                ));
            }
            placed.push((fin.clone(), align));
            functions.push(serde_json::json!({
                "name": f["symbol"],
                "final": fin,
                "dump": dump,
                "ra": ra,
            }));
        }
        nfuncs += functions.len();
        aligns.extend(region_aligns(&placed));
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
        "aligns": aligns.iter().map(|(n, a)| serde_json::json!([n, a])).collect::<Vec<_>>(),
        "skipped": skipped,
    });
    let bp = o.out.join("bundle.json");
    fs::write(&bp, serde_json::to_string_pretty(&bundle).unwrap_or_default())
        .map_err(|e| format!("{}: {e}", bp.display()))?;
    eprintln!(
        "cargo fv link-proof: {nfuncs} functions of {} codegen unit(s) of {exe} ({}; skipped {}, left out of the region {n_excluded}), {} executable symbols → {}",
        cgus.len(),
        match (&o.cgus, &list) {
            (Some(_), _) => "the units --cgus lists",
            (None, Some(_)) => "the region's units, as lean-link placed them",
            (None, None) => "the units whose object the link map names",
        },
        skipped.len(),
        symbols.len(),
        bp.display()
    );
    // #1130: the Lean-compiled functions of the executable (their markers are in the link map)
    // that are not in the bundle, by codegen unit
    let named: BTreeSet<&str> = skipped.iter().map(|(n, _)| n.as_str()).collect();
    let missing = not_in_bundle(map.syms.keys().map(String::as_str), &markers, &named);
    if !missing.is_empty() {
        let by_unit: Vec<String> = units_of(&tmp, &missing)
            .into_iter()
            .map(|(obj, n)| match obj {
                Some(obj) => {
                    let why = if map.objects.contains(&obj) { "its object is linked" } else { "its object is not in the link map" };
                    format!("{obj} ({n}; {why})")
                }
                None => format!("no kept codegen unit ({n})"),
            })
            .collect();
        eprintln!(
            "cargo fv link-proof: {exe}: {} Lean-compiled function(s) of the executable (their {MARKER} markers are in the link map) {NOT_IN_BUNDLE}: {} unit(s): {}; first: {}",
            missing.len(),
            by_unit.len(),
            by_unit.join(", "),
            missing[0]
        );
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn fns(l: &[(&str, u64)]) -> Vec<(String, u64)> {
        l.iter().map(|(n, a)| (n.to_string(), *a)).collect()
    }

    #[test]
    fn region_aligns_word_units_list_nothing() {
        assert!(region_aligns(&fns(&[("a", 4), ("b", 4)])).is_empty());
        assert!(region_aligns(&[]).is_empty());
    }

    #[test]
    fn region_aligns_pooled_function_and_unit_start() {
        // a pooled function (8) later in its unit: `ld -r` 8-aligns it and the unit's start
        assert_eq!(region_aligns(&fns(&[("a", 4), ("p", 8), ("b", 4)])), fns(&[("a", 8), ("p", 8)]));
        // first in its unit: listed once
        assert_eq!(region_aligns(&fns(&[("p", 8), ("b", 4)])), fns(&[("p", 8)]));
        // a 16-byte constant pool (SIMD) raises the unit's start to 16
        assert_eq!(region_aligns(&fns(&[("a", 4), ("p", 8), ("q", 16)])), fns(&[("a", 16), ("p", 8), ("q", 16)]));
    }

    /// #1130: a unit whose own object the link did not take (an archive member the region object
    /// makes unnecessary) is in the region's list, so it is in the bundle; without a list (no
    /// `--lean-link`: the Lean code is inside the unit's object) only the linked units are.
    #[test]
    fn region_list_keeps_units_the_link_did_not_take() {
        let tmp = std::env::temp_dir().join(format!("cargo-fv-units-{}", std::process::id()));
        let _ = fs::remove_dir_all(&tmp);
        for (d, obj) in [("u1", "a-1.a.0-cgu.0.rcgu.o"), ("u2", "zerocopy-2.zerocopy.0-cgu.0.rcgu.o")] {
            fs::create_dir_all(tmp.join(d)).unwrap();
            fs::write(tmp.join(d).join(CGU_FILE), format!("{{\"object\": \"{obj}\", \"functions\": []}}")).unwrap();
        }
        let list = tmp.join("cgus.txt");
        fs::write(&list, format!("{}\n{}\n", tmp.join("u2").display(), tmp.join("u1").display())).unwrap();
        let linked: BTreeSet<String> = ["a-1.a.0-cgu.0.rcgu.o".to_string()].into();
        let objs = |l: Option<&Path>, k: Option<&str>| -> Vec<String> {
            select_units(&tmp, l, &linked, k).unwrap().into_iter().map(|(o, _, _)| o).collect()
        };
        assert_eq!(objs(Some(&list), None), ["zerocopy-2.zerocopy.0-cgu.0.rcgu.o", "a-1.a.0-cgu.0.rcgu.o"]);
        assert_eq!(objs(Some(&list), Some("a")), ["a-1.a.0-cgu.0.rcgu.o"]);
        assert_eq!(objs(None, None), ["a-1.a.0-cgu.0.rcgu.o"]);
        let _ = fs::remove_dir_all(&tmp);
    }

    /// #1130: the markers of the link map that the bundle lacks are named, the skipped ones are
    /// reported as skipped instead; other symbols are not functions.
    #[test]
    fn functions_not_in_the_bundle() {
        let bundle: BTreeMap<String, u64> = [("f".to_string(), 0x10)].into();
        let skipped: BTreeSet<&str> = ["s"].into();
        let syms = ["__fvlean$f", "__fvlean$g", "__fvlean$s", "__fvlean$h", "__fvlean$g", "f", "__fvlean_start"];
        assert_eq!(not_in_bundle(syms.into_iter(), &bundle, &skipped), ["g", "h"]);
        assert!(not_in_bundle(["__fvlean$f", "f"].into_iter(), &bundle, &skipped).is_empty());
    }
}
