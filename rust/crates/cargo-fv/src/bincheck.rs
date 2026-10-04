//! `cargo fv build`'s per-executable binary check (docs/contracts/e2e.md, "Binary level (M9)"):
//! after a build, every linked executable's Lean-compiled functions go through `cargo fv
//! link-proof` (its directory under `target/fv/<mode>/bin-check/`) and `lake exe link-check
//! --prune`, which decides the premises of `E2E.Binary.binary_correct`: `LinkSys.Ok` (`okB`),
//! the executable's code, data and symbols against the proven program (`binary:`), and the stack
//! bound (`stack:`). The verdict is printed next to the per-function report.
use std::path::Path;
use std::process::Command;

use crate::pipeline::tag_of;

/// The verdict on one executable.
pub struct Verdict {
    /// `binary_correct` holds for every Lean-compiled function of the executable.
    pub verified: bool,
    /// One line: what holds, or the failing check.
    pub summary: String,
}

/// The value of `key` in `line` (`  key: value`).
fn field<'a>(out: &'a str, key: &str) -> Option<&'a str> {
    out.lines().find_map(|l| l.trim_start().strip_prefix(key))
}

/// The verdict from `link-check`'s output (`ok`: its exit status was 0).
pub fn verdict_of(out: &str, ok: bool) -> Verdict {
    let not = |s: String| Verdict { verified: false, summary: s };
    if field(out, "link-check: ").is_none() {
        // `cargo fv link-proof` stopped before the checker (no kept codegen unit, …)
        let msg = out.lines().rev().find(|l| !l.trim().is_empty()).unwrap_or("no output").trim();
        return not(format!("not checked: {msg}"));
    }
    let (pass, total) = field(out, "--prune: ")
        .and_then(|v| {
            let mut w = v.split_whitespace();
            let p = w.next()?.parse::<usize>().ok()?;
            let t = w.nth(1)?.parse::<usize>().ok()?;
            Some((p, t))
        })
        .unwrap_or((0, 0));
    let stack = field(out, "stack: ").map(|s| format!("; stack: {s}")).unwrap_or_default();
    let first_fail = out
        .lines()
        .position(|l| l.trim_start().starts_with("FAIL "))
        .map(|i| {
            let lines: Vec<&str> = out.lines().collect();
            let f = lines[i].trim().trim_start_matches("FAIL ").trim_end_matches(':');
            match lines.get(i + 1) {
                Some(p) => format!("{f}: {}", p.trim()),
                None => f.to_string(),
            }
        });
    match field(out, "binary: ") {
        Some(b) if b.starts_with("ok") => {}
        Some(b) => {
            let detail = out.lines().find(|l| l.trim_start().starts_with("BIN ")).map(|l| format!(" — {}", l.trim())).unwrap_or_default();
            return not(format!("not verified: binary check failed: {b}{detail}"));
        }
        None => return not("not verified: link-check ran no binary check (lake build link-check)".into()),
    }
    if !ok || field(out, "okB: ") != Some("true") {
        return not(format!("not verified: the crate checker fails (okB){}", first_fail.map(|f| format!(": {f}")).unwrap_or_default()));
    }
    if pass < total {
        return not(format!(
            "not verified: {} of {total} Lean-compiled functions fail (first: {}); binary_correct holds for the other {pass}{stack}",
            total - pass,
            first_fail.unwrap_or_else(|| "?".into())
        ));
    }
    Verdict { verified: true, summary: format!("verified: E2E.Binary.binary_correct holds for its {total} Lean-compiled functions{stack}") }
}

/// Check the executable `exe` linked in the build under `fv_dir` (`target/fv/<mode>`).
pub fn check(fv_dir: &Path, exe: &str, manifest: Option<&str>) -> Verdict {
    let not = |s: String| Verdict { verified: false, summary: s };
    let Ok(me) = std::env::current_exe() else { return not("not checked: cargo-fv's path is unknown".into()) };
    let mode = fv_dir.file_name().map(|m| m.to_string_lossy().into_owned()).unwrap_or_default();
    let out_dir = fv_dir.join("bin-check").join(tag_of(exe));
    let mut cmd = Command::new(me);
    cmd.arg("link-proof").arg("--exe").arg(exe).arg("--out").arg(&out_dir).arg("--prune").arg("--mode").arg(&mode);
    if let Some(m) = manifest {
        cmd.arg("--manifest-path").arg(m);
    }
    match cmd.output() {
        Ok(o) => {
            let mut text = String::from_utf8_lossy(&o.stdout).into_owned();
            text.push_str(&String::from_utf8_lossy(&o.stderr));
            verdict_of(&text, o.status.success())
        }
        Err(e) => not(format!("not checked: {e}")),
    }
}
