//! `clif-results`: counts and compares run-command results in the clif-oracle JSON-lines
//! schema (`docs/contracts/clif.md`), as printed by `clif-oracle interp` and `clif-native`.
//!
//! * `clif-results summary [-v] FILE.json...` — per file and in total: runs whose outcome
//!   meets the `==`/`!=` expectation (`pass`), runs that do not (`fail`: other values, or a
//!   trap), `; print` commands (`print`), `{"error"}` outcomes (`error`), errors whose
//!   message starts with `not compiled:` (`not-compiled`: `clif-native` could not run the
//!   function because Cranelift rejects it for aarch64) and whole-file failures
//!   (`file-error`). Exit status 0 iff there is no fail, error or file error.
//! * `clif-results compare [-v] DIR_A DIR_B` — for every `*.json` in `DIR_A`, compares its
//!   records with the file of the same name in `DIR_B` in order: the records must be for the
//!   same command (`attached`, `func`, `args`); they `agree` iff their `actual` outcomes are
//!   equal, otherwise they `disagree` — unless one side is an `{"error"}` (the engine did
//!   not run the command), which counts as `error`. Exit status 0 iff every record has a
//!   counterpart and there is no disagreement.

use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{Context, Result, bail};
use serde_json::Value;

fn read_records(path: &Path) -> Result<Vec<Value>> {
    let text = std::fs::read_to_string(path).with_context(|| format!("reading {}", path.display()))?;
    text.lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).with_context(|| format!("{}: bad JSON line {l}", path.display())))
        .collect()
}

fn describe(rec: &Value) -> String {
    let args: Vec<String> = rec["args"]
        .as_array()
        .map(|a| a.iter().map(|v| format!("{}:{}", v["bits"].as_str().unwrap_or("?"), v["ty"].as_str().unwrap_or("?"))).collect())
        .unwrap_or_default();
    format!("%{}({})", rec["func"].as_str().unwrap_or("?"), args.join(", "))
}

#[derive(Default)]
struct Counts {
    pass: usize,
    fail: usize,
    print: usize,
    error: usize,
    not_compiled: usize,
    file_error: usize,
}

impl Counts {
    fn add(&mut self, o: &Counts) {
        self.pass += o.pass;
        self.fail += o.fail;
        self.print += o.print;
        self.error += o.error;
        self.not_compiled += o.not_compiled;
        self.file_error += o.file_error;
    }
    fn line(&self) -> String {
        format!(
            "pass {} fail {} print {} error {} not-compiled {} file-error {}",
            self.pass, self.fail, self.print, self.error, self.not_compiled, self.file_error
        )
    }
}

fn summary(verbose: bool, files: &[PathBuf]) -> Result<bool> {
    let mut total = Counts::default();
    for f in files {
        let mut c = Counts::default();
        let mut notes = Vec::new();
        for rec in read_records(f)? {
            if let Some(e) = rec.get("file_error") {
                c.file_error += 1;
                notes.push(format!("  file error: {e}"));
                continue;
            }
            let actual = &rec["actual"];
            if let Some(e) = actual.get("error") {
                if e.as_str().is_some_and(|m| m.starts_with("not compiled:")) {
                    c.not_compiled += 1;
                    notes.push(format!("  not compiled {}: {e}", describe(&rec)));
                } else {
                    c.error += 1;
                    notes.push(format!("  error {}: {e}", describe(&rec)));
                }
                continue;
            }
            let expected = &rec["expected"];
            if expected.is_null() {
                c.print += 1;
                continue;
            }
            let returned = actual.get("returned");
            let same = returned == Some(&expected["values"]);
            let ok = match expected["cmp"].as_str() {
                Some("==") => same,
                Some("!=") => returned.is_some() && !same,
                other => bail!("{}: unknown comparison {other:?}", f.display()),
            };
            if ok {
                c.pass += 1;
            } else {
                c.fail += 1;
                notes.push(format!("  fail {}: expected {} {}, got {actual}", describe(&rec), expected["cmp"], expected["values"]));
            }
        }
        println!("{}: {}", f.display(), c.line());
        if verbose {
            for n in notes {
                println!("{n}");
            }
        }
        total.add(&c);
    }
    println!("TOTAL files {}: {}", files.len(), total.line());
    Ok(total.fail == 0 && total.error == 0 && total.file_error == 0)
}

fn same_command(a: &Value, b: &Value) -> bool {
    a.get("file_error").is_none()
        && b.get("file_error").is_none()
        && a["attached"] == b["attached"]
        && a["func"] == b["func"]
        && a["args"] == b["args"]
}

fn compare(verbose: bool, dir_a: &Path, dir_b: &Path) -> Result<bool> {
    let mut names: Vec<_> = std::fs::read_dir(dir_a)
        .with_context(|| format!("reading {}", dir_a.display()))?
        .filter_map(|e| e.ok().map(|e| e.file_name()))
        .filter(|n| n.to_string_lossy().ends_with(".json"))
        .collect();
    names.sort();
    let (mut records, mut agree, mut disagree, mut errors, mut unmatched) = (0, 0, 0, 0, 0);
    for name in &names {
        let a = read_records(&dir_a.join(name))?;
        let pb = dir_b.join(name);
        let b = if pb.exists() { read_records(&pb)? } else { Vec::new() };
        let (mut fa, mut fd, mut fe, mut fu) = (0, 0, 0, 0);
        let mut notes = Vec::new();
        for (i, ra) in a.iter().enumerate() {
            match b.get(i) {
                Some(rb) if same_command(ra, rb) => {
                    if ra["actual"] == rb["actual"] {
                        fa += 1;
                    } else if ra["actual"].get("error").is_some() || rb["actual"].get("error").is_some() {
                        fe += 1;
                        notes.push(format!("  error {}: {} vs {}", describe(ra), ra["actual"], rb["actual"]));
                    } else {
                        fd += 1;
                        notes.push(format!("  disagree {}: {} vs {}", describe(ra), ra["actual"], rb["actual"]));
                    }
                }
                _ => {
                    fu += 1;
                    notes.push(format!("  unmatched record {i}: {ra}"));
                }
            }
        }
        fu += b.len().saturating_sub(a.len());
        records += a.len();
        agree += fa;
        disagree += fd;
        errors += fe;
        unmatched += fu;
        if verbose || fd + fe + fu > 0 {
            println!("{}: agree {fa} disagree {fd} error {fe} unmatched {fu}", name.to_string_lossy());
            if verbose {
                for n in notes {
                    println!("{n}");
                }
            }
        }
    }
    println!(
        "TOTAL files {}: records {records} agree {agree} disagree {disagree} error {errors} unmatched {unmatched}",
        names.len()
    );
    Ok(disagree == 0 && unmatched == 0)
}

const USAGE: &str = "usage: clif-results summary [-v] FILE.json... | clif-results compare [-v] DIR_A DIR_B";

fn run() -> Result<bool> {
    let mut args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        bail!("{USAGE}");
    }
    let cmd = args.remove(0);
    let verbose = args.first().is_some_and(|a| a == "-v");
    if verbose {
        args.remove(0);
    }
    match (cmd.as_str(), args.as_slice()) {
        ("summary", files) => summary(verbose, &files.iter().map(PathBuf::from).collect::<Vec<_>>()),
        ("compare", [a, b]) => compare(verbose, Path::new(a), Path::new(b)),
        _ => bail!("{USAGE}"),
    }
}

fn main() -> ExitCode {
    match run() {
        Ok(true) => ExitCode::SUCCESS,
        Ok(false) => ExitCode::FAILURE,
        Err(e) => {
            eprintln!("clif-results: {e:#}");
            ExitCode::from(2)
        }
    }
}
