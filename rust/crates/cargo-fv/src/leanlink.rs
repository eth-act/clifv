//! `--lean-link` (L2b, docs/research/lean-linker.md): the Lean linker writes the program part
//! of an executable.
//!
//! With `--lean-link` the codegen units keep cg_clif's object with our functions weak and the
//! renamed symbols global ([`crate::pipeline`]); every unit's Lean code stays in its work
//! directory (`lean.o`: the functions in order, each followed by a zero gap word). At the
//! executable's link:
//!
//! 1. [`program_part`]: the work directories of the units linked (the unit's own objects and
//!    the members of the rlibs), sorted by object name; `ld -r` of their `lean.o` gives one
//!    object whose `.text.fvlean` section is the region, laid out as `Link.offs` places it, its
//!    functions strong (they win over cg_clif's weak copies) and their `.eh_frame` entries;
//! 2. rust-lld links the outside part around it (`-u __fvlean_start` keeps the region);
//! 3. [`patch`]: `cargo fv link-proof --cgus … --no-check` writes the Lean linker's input (the
//!    functions' CLIF and allocations, the outside part's symbol addresses); `lake exe
//!    lean-link` computes the region's bytes (`Link.leanLink`: placement, relocation, checks)
//!    and writes them into the executable.
use crate::config::Config;
use crate::pipeline::run;
use object::read::archive::ArchiveFile;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

/// The symbol at the start of the region.
pub const START: &str = "__fvlean_start";

/// The object names an executable's link takes: its own `.rcgu.o` files and the members of
/// its rlibs.
fn input_objects(args: &[String]) -> Result<BTreeSet<String>, String> {
    let mut s = BTreeSet::new();
    for a in args {
        let p = Path::new(a);
        let Some(n) = p.file_name().map(|n| n.to_string_lossy().into_owned()) else { continue };
        if n.ends_with(".rcgu.o") {
            s.insert(n);
        } else if n.ends_with(".rlib") {
            let data = fs::read(p).map_err(|e| format!("{a}: {e}"))?;
            let ar = ArchiveFile::parse(&*data).map_err(|e| format!("{a}: {e}"))?;
            for m in ar.members() {
                let m = m.map_err(|e| format!("{a}: {e}"))?;
                s.insert(String::from_utf8_lossy(m.name()).into_owned());
            }
        }
    }
    Ok(s)
}

/// The program part of the link with arguments `args`: the region's object and the file
/// listing its units' work directories (in placement order); `None` without Lean-compiled code.
pub fn program_part(cfg: &Config, unit: &str, args: &[String]) -> Result<Option<(PathBuf, PathBuf)>, String> {
    let objs = input_objects(args)?;
    // object name → (fv-link.json's modification time, work directory): the newest
    let mut dirs: BTreeMap<String, (std::time::SystemTime, PathBuf)> = BTreeMap::new();
    for e in fs::read_dir(&cfg.tmp_dir).map_err(|e| format!("{}: {e}", cfg.tmp_dir.display()))?.flatten() {
        let p = e.path().join(crate::linkproof::CGU_FILE);
        let Ok(text) = fs::read_to_string(&p) else { continue };
        let j: serde_json::Value = serde_json::from_str(&text).map_err(|e| format!("{}: {e}", p.display()))?;
        let obj = j["object"].as_str().unwrap_or_default().to_string();
        if !objs.contains(&obj) {
            continue;
        }
        let t = fs::metadata(&p).and_then(|m| m.modified()).map_err(|e| format!("{}: {e}", p.display()))?;
        if dirs.get(&obj).is_none_or(|(t0, _)| *t0 < t) {
            dirs.insert(obj, (t, e.path()));
        }
    }
    if dirs.is_empty() {
        return Ok(None);
    }
    let work = cfg.tmp_dir.join(format!("leanlink-{}", crate::pipeline::tag_of(unit)));
    let _ = fs::remove_dir_all(&work);
    fs::create_dir_all(&work).map_err(|e| format!("{}: {e}", work.display()))?;
    let leans: Vec<PathBuf> = dirs.values().map(|(_, d)| d.join("lean.o")).collect();
    // named as one of the unit's own objects (the report attributes its code to the unit)
    let obj = work.join(format!("{unit}.fvlean.rcgu.o"));
    run(Command::new(&cfg.rust_lld).args(["-flavor", "gnu", "-r", "-o"]).arg(&obj).args(&leans))?;
    run(Command::new(&cfg.objcopy).arg("--rename-section").arg(".text=.text.fvlean").arg(&obj))?;
    run(Command::new(&cfg.objcopy).arg(format!("--add-symbol={START}=.text.fvlean:0,global")).arg(&obj))?;
    let list = work.join("cgus.txt");
    let text: String = dirs.values().map(|(_, d)| format!("{}\n", d.display())).collect();
    fs::write(&list, text).map_err(|e| format!("{}: {e}", list.display()))?;
    write_sizes(&obj, &work.join(SIZES))?;
    Ok(Some((obj, list)))
}

/// The region's sizes file (in the work directory, next to `cgus.txt`).
const SIZES: &str = "sizes.txt";

/// One line `NAME WORDS` per function of the region object `obj`: its words up to the next
/// function, the gap word excluded (`Link.offs`; `Link.leanLink` checks them, `sizesOkB`).
fn write_sizes(obj: &Path, out: &Path) -> Result<(), String> {
    use object::read::{Object, ObjectSection, ObjectSymbol};
    let data = fs::read(obj).map_err(|e| format!("{}: {e}", obj.display()))?;
    let file = object::File::parse(&*data).map_err(|e| format!("{}: {e}", obj.display()))?;
    let sec = file.section_by_name(".text.fvlean").ok_or_else(|| format!("{}: no .text.fvlean", obj.display()))?;
    let mut fns: Vec<(u64, String)> = Vec::new();
    for s in file.symbols() {
        let Ok(n) = s.name() else { continue };
        if s.section_index() == Some(sec.index())
            && s.kind() == object::SymbolKind::Text
            && s.is_global()
            && !n.starts_with(crate::pipeline::MARKER)
            && n != START
        {
            fns.push((s.address(), n.to_string()));
        }
    }
    fns.sort();
    let mut text = String::new();
    for (k, (a, n)) in fns.iter().enumerate() {
        let end = fns.get(k + 1).map_or(sec.size(), |x| x.0);
        if end < a + 4 {
            return Err(format!("{}: `{n}` has no gap word", obj.display()));
        }
        text.push_str(&format!("{n} {}\n", (end - a - 4) / 4));
    }
    fs::write(out, text).map_err(|e| format!("{}: {e}", out.display()))
}

/// Write the program part into the linked executable `exe` (its link map recorded by the
/// linker mode as `link-<tag>.json`): the Lean linker's input, then `lake exe lean-link`.
pub fn patch(cfg: &Config, exe: &Path, list: &Path) -> Result<String, String> {
    let fv_dir = cfg.tmp_dir.parent().ok_or("no target/fv/<mode> directory")?;
    let target = fv_dir.parent().and_then(|p| p.parent()).ok_or("no target directory")?;
    let mode = fv_dir.file_name().map(|m| m.to_string_lossy().into_owned()).unwrap_or_default();
    let dir = list.parent().ok_or("no work directory")?.join("input");
    let args: Vec<String> = vec![
        "--exe".into(),
        exe.display().to_string(),
        "--out".into(),
        dir.display().to_string(),
        "--mode".into(),
        mode,
        "--cgus".into(),
        list.display().to_string(),
        "--no-check".into(),
    ];
    crate::linkproof::run(target, &cfg.root, &args)?;
    let tool = cfg.root.join(".lake/build/bin/lean-link");
    let sizes = list.parent().ok_or("no work directory")?.join(SIZES);
    let out = Command::new(&tool)
        .arg(&dir)
        .arg(&sizes)
        .output()
        .map_err(|e| format!("{}: {e} (lake build lean-link)", tool.display()))?;
    let text = String::from_utf8_lossy(&out.stdout).into_owned() + &String::from_utf8_lossy(&out.stderr);
    if !out.status.success() {
        return Err(format!("lean-link failed:\n{text}"));
    }
    Ok(text)
}
