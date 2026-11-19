//! `cargo fv build`'s per-executable binary check (docs/contracts/e2e.md, "Binary level (M9)"):
//! after a build, every linked executable's Lean-compiled functions go through `cargo fv
//! link-proof` (its directory under `target/fv/<mode>/bin-check/`) and `lake exe link-check
//! --prune`, which decides the premises of an executable-word theorem about the program's results
//! in its checker: the checker (`okB:`), the executable's code, data and symbols against the
//! proven program (`binary:`), the code map (`code map:`), the GOT slots (`GOT:`) and the stack
//! bound (`stack:`), and names the theorem they instantiate (`theorem:`, `FVTest/E2E/BinVerdict.lean`).
//! The verdict is printed next to the per-function report.
use std::path::Path;
use std::process::Command;

use crate::linkproof::NOT_IN_BUNDLE;
use crate::pipeline::tag_of;

/// The verdict on one executable.
pub struct Verdict {
    /// The theorem `link-check` names holds for every Lean-compiled function of the executable.
    pub verified: bool,
    /// One line: what holds, or the failing check.
    pub summary: String,
    /// The number of functions the named theorem's instance covers (the program the binary
    /// check passed: `link-check`'s `--prune` count of passing functions); `None` when no
    /// theorem is named.
    pub checked: Option<usize>,
}

/// The binary check's verdict `v` against the number of Lean-compiled functions in the
/// executable, `total` (`what`: whose count it is: lean-link's region count, or with the
/// Lean code in cg_clif's objects the markers resolved in the executable). The executable is
/// verified only when the theorem's instance covers every one of them; a different count is
/// named in the summary, whatever the verdict (#1130).
pub fn cover(v: Verdict, total: usize, what: &str) -> Verdict {
    match v.checked {
        Some(n) if n != total => {
            let diff = format!("the binary check covers {n} function(s), the executable has {total} Lean-compiled function(s) ({what})");
            let summary = match v.summary.strip_prefix("verified: ") {
                Some(s) if v.verified => format!("not verified: {diff}; {s}"),
                _ => format!("{}; {diff}", v.summary),
            };
            Verdict { verified: false, summary, checked: v.checked }
        }
        _ => v,
    }
}

/// The value of `key` in `line` (`  key: value`).
fn field<'a>(out: &'a str, key: &str) -> Option<&'a str> {
    out.lines().find_map(|l| l.trim_start().strip_prefix(key))
}

/// Why `link-check` stopped without a `binary:` line: its last `link-check: ` line other than
/// the header `link-check: <exe>`, without the executable's name. `link-check: <exe>: <message>`
/// when the bundle cannot be assembled (e.g. `link-proof skipped N function(s) of the region:
/// <first>: <why>`); `link-check: <message>` when it cannot be read, before any header. The
/// header and the messages are on different streams, so in either order.
fn stop_reason<'a>(out: &'a str, exe: &str) -> Option<&'a str> {
    out.lines()
        .filter_map(|l| l.trim_start().strip_prefix("link-check: "))
        .filter(|l| *l != exe)
        .map(|l| l.strip_prefix(exe).and_then(|r| r.strip_prefix(": ")).unwrap_or(l))
        .last()
}

/// The verdict on `exe` from `link-check`'s output (`ok`: its exit status was 0). A function of
/// the executable that `cargo fv link-proof` names as not in the bundle ([`NOT_IN_BUNDLE`]) is not
/// covered by the theorem: the executable is not verified, and the summary names them (#1130).
pub fn verdict_of(out: &str, ok: bool, exe: &str) -> Verdict {
    let v = verdict_in(out, ok, exe);
    let Some(gap) = out.lines().find(|l| l.contains(NOT_IN_BUNDLE)) else { return v };
    let gap = gap.trim_start().strip_prefix("cargo fv link-proof: ").unwrap_or(gap.trim());
    let gap = gap.strip_prefix(exe).and_then(|g| g.strip_prefix(": ")).unwrap_or(gap);
    let summary = match v.summary.strip_prefix("verified: ") {
        Some(s) if v.verified => format!("not verified: {gap}; {s}"),
        _ => format!("{}; {gap}", v.summary),
    };
    Verdict { verified: false, summary, checked: v.checked }
}

fn verdict_in(out: &str, ok: bool, exe: &str) -> Verdict {
    let not = |s: String| Verdict { verified: false, summary: s, checked: None };
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
    // the stack line without its list of recursive functions
    let stack = field(out, "stack: ")
        .map(|s| match (s.find(": ["), s.find("; the other")) {
            (Some(i), Some(j)) if i < j => format!("; stack: {}{}", &s[..i], &s[j..]),
            _ => format!("; stack: {s}"),
        })
        .unwrap_or_default();
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
        None => {
            return not(match stop_reason(out, exe) {
                Some(why) if why.starts_with("link-proof skipped ") => format!(
                    "not verified: link-check stopped before the binary check: {why} (the executable links \
                     Lean-compiled code that is unverified, so it is not the proven program; `cargo fv report \
                     --functions` lists the unverified functions, and --lean-link --verified keeps cg_clif's \
                     code for them)"
                ),
                Some(why) => format!("not verified: link-check stopped before the binary check: {why}"),
                None => "not verified: link-check stopped before the binary check without a reason".into(),
            })
        }
    }
    if !ok || field(out, "okB: ") != Some("true") {
        // link-check's exit status also covers the code map and the GOT check (#1093)
        if field(out, "okB: ") == Some("true") {
            if field(out, "code map: ") != Some("ok") {
                return not("not verified: the code map check fails (codeMapB)".into());
            }
            if !field(out, "GOT: ").is_some_and(|g| g.starts_with("ok")) {
                return not(format!("not verified: the GOT check fails (GotOk): {}", field(out, "GOT: ").unwrap_or("no GOT line")));
            }
        }
        return not(format!("not verified: the crate checker fails (okB){}", first_fail.map(|f| format!(": {f}")).unwrap_or_default()));
    }
    // the theorem link-check's checks instantiate, named by link-check next to them (#1092,
    // `FVTest/E2E/BinVerdict.lean`): only when every premise it decides holds
    let which = match field(out, "theorem: ") {
        Some(t) if !t.starts_with("none") => t,
        Some(t) => return not(format!("not verified: {t}")),
        None => return not("not verified: link-check names no theorem".into()),
    };
    if pass < total {
        return Verdict {
            verified: false,
            summary: format!(
                "not verified: {} of {total} Lean-compiled functions fail (first: {}); {which} holds for the other {pass}{stack}",
                total - pass,
                first_fail.unwrap_or_else(|| "?".into())
            ),
            checked: Some(pass),
        };
    }
    Verdict {
        verified: true,
        summary: format!("verified: {which} holds for its {total} Lean-compiled functions{stack}"),
        checked: Some(total),
    }
}

/// Check the executable `exe` linked in the build under `fv_dir` (`target/fv/<mode>`).
pub fn check(fv_dir: &Path, exe: &str, manifest: Option<&str>) -> Verdict {
    let not = |s: String| Verdict { verified: false, summary: s, checked: None };
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
            verdict_of(&text, o.status.success(), exe)
        }
        Err(e) => not(format!("not checked: {e}")),
    }
}

#[cfg(test)]
mod tests {
    use super::{cover, verdict_of};
    use crate::linkproof::NOT_IN_BUNDLE;

    const EXE: &str = "/w/target/fv/plain/aarch64-unknown-linux-musl/debug/build/bigframe-unwind/938e46b67ec0fe2f/out/bigframe_unwind-938e46b67ec0fe2f";
    const SKIPPED: &str = "link-proof skipped 1 function(s) of the region: __fv_e90dc2697494__RNxC15bigframe_unwind12H1IxI06hs9Qw: unverified: outside clif-subset-v2 E";

    /// #1008: link-check stops at an unverified function of the region (examples/bigframe-unwind).
    /// The verdict names the function and the reason, not a missing tool.
    #[test]
    fn skipped_function_is_the_reason() {
        let link_proof = format!("cargo fv link-proof: 74 functions of 2 codegen unit(s) of {EXE} (skipped 1, left out of the region 0), 2554 executable symbols → /w/bin-check/bundle.json\n");
        // `check` appends stderr to stdout; a log with both streams merged has the header last
        for out in [
            format!("link-check: {EXE}\n{link_proof}link-check: {EXE}: {SKIPPED}\n"),
            format!("{link_proof}link-check: {EXE}: {SKIPPED}\nlink-check: {EXE}\n"),
        ] {
            let v = verdict_of(&out, false, EXE);
            assert!(!v.verified);
            assert!(v.summary.starts_with(&format!("not verified: link-check stopped before the binary check: {SKIPPED} (")), "{}", v.summary);
            assert!(!v.summary.contains("lake build"), "{}", v.summary);
        }
    }

    #[test]
    fn other_stops() {
        // another message of link-check after its header
        let v = verdict_of(&format!("link-check: {EXE}\nlink-check: {EXE}: unit a-1: no data.clif\n"), false, EXE);
        assert_eq!(v.summary, "not verified: link-check stopped before the binary check: unit a-1: no data.clif");
        // only the header (link-check died)
        let v = verdict_of(&format!("link-check: {EXE}\n"), false, EXE);
        assert_eq!(v.summary, "not verified: link-check stopped before the binary check without a reason");
        // review finding (CiGate2Review 2): link-check cannot read the bundle and stops before
        // its header; the one line is the reason, not a header to drop
        let v = verdict_of("link-check: /w/bin-check/bundle.json: unexpected end of input\n", false, EXE);
        assert_eq!(v.summary, "not verified: link-check stopped before the binary check: /w/bin-check/bundle.json: unexpected end of input");
        // link-check did not run: `cargo fv link-proof` stopped first
        let v = verdict_of("cargo fv: no linked executable in /w/tmp (build with --keep-temps)\n", false, EXE);
        assert!(v.summary.starts_with("not checked: "), "{}", v.summary);
    }

    #[test]
    fn verified_and_failing() {
        let ok = format!(
            "link-check: {EXE}\n  checker: integer\n  okB: true\n  --prune: 74 of 74 functions pass (0 dropped)\n  binary: ok\n  code map: ok\n  GOT: ok (0 GOT pair(s) with an ldr; 0 ms)\n  stack: 352 bytes at most (no call cycle)\n  theorem: E2E.ReturnPinExecBytes.binary_correct_exec_proven\n"
        );
        let v = verdict_of(&ok, true, EXE);
        assert!(v.verified, "{}", v.summary);
        assert!(v.summary.starts_with("verified: E2E.ReturnPinExecBytes.binary_correct_exec_proven holds for its 74 Lean-compiled functions"), "{}", v.summary);
        let pruned = ok.replace("74 of 74 functions pass (0 dropped)", "71 of 74 functions pass (3 dropped)");
        let v = verdict_of(&pruned, true, EXE);
        assert!(!v.verified);
        assert!(v.summary.starts_with("not verified: 3 of 74 Lean-compiled functions fail"), "{}", v.summary);
        assert!(v.summary.contains("E2E.ReturnPinExecBytes.binary_correct_exec_proven holds for the other 71"), "{}", v.summary);
        let v = verdict_of(&ok.replace("binary: ok", "binary: FAIL 2 excerpts"), true, EXE);
        assert!(v.summary.starts_with("not verified: binary check failed: FAIL 2 excerpts"), "{}", v.summary);
    }

    /// #1093: a failing code map or GOT check is not verified; link-check then names no theorem
    /// and exits 1.
    #[test]
    fn code_map_and_got() {
        let ok = format!(
            "link-check: {EXE}\n  checker: typed Stock (okRWithTS)\n  okB: true\n  --prune: 5 of 5 functions pass (0 dropped)\n  binary: ok\n  code map: ok\n  GOT: ok (0 GOT pair(s) with an ldr; 0 ms)\n  stack: 64 bytes at most (no call cycle)\n  theorem: E2E.SemanticExecBytes.binary_correct_exec_provenTS\n"
        );
        assert!(verdict_of(&ok, true, EXE).verified);
        let cm = ok
            .replace("code map: ok", "code map: FAIL (codeMapB)")
            .replace("theorem: E2E.SemanticExecBytes.binary_correct_exec_provenTS", "theorem: none (codeMapB fails)");
        let v = verdict_of(&cm, false, EXE);
        assert!(!v.verified);
        assert_eq!(v.summary, "not verified: the code map check fails (codeMapB)");
        let got = ok
            .replace("GOT: ok (0", "GOT: FAIL (GotOk) (1")
            .replace("theorem: E2E.SemanticExecBytes.binary_correct_exec_provenTS", "theorem: none (GotOk fails)");
        let v = verdict_of(&got, false, EXE);
        assert!(!v.verified);
        assert!(v.summary.starts_with("not verified: the GOT check fails (GotOk)"), "{}", v.summary);
        // an older link-check without the theorem line: not verified
        let v = verdict_of(&ok.replace("  theorem: E2E.SemanticExecBytes.binary_correct_exec_provenTS\n", ""), true, EXE);
        assert!(!v.verified);
        assert_eq!(v.summary, "not verified: link-check names no theorem");
    }

    /// #1130: the theorem link-check names covers the bundle's functions; when the executable has
    /// more Lean-compiled functions (lean-link's region count) the executable is not verified and
    /// the summary names both counts. An equal count keeps the verdict.
    #[test]
    fn region_count_difference() {
        const OK: &str = "link-check: X\n  okB: true\n  --prune: 74 of 74 functions pass (0 dropped)\n  binary: ok\n  code map: ok\n  GOT: ok (0 GOT pair(s) with an ldr; 0 ms)\n  stack: 352 bytes at most (no call cycle)\n  theorem: E2E.ReturnPinExecBytes.binary_correct_exec_proven\n";
        let ok = OK.replace('X', EXE);
        let v = cover(verdict_of(&ok, true, EXE), 74, "lean-link's region count");
        assert!(v.verified, "{}", v.summary);
        assert_eq!(v.checked, Some(74));
        let v = cover(verdict_of(&ok, true, EXE), 79, "lean-link's region count");
        assert!(!v.verified);
        assert_eq!(v.checked, Some(74));
        assert!(
            v.summary.starts_with("not verified: the binary check covers 74 function(s), the executable has 79 Lean-compiled function(s) (lean-link's region count); E2E.ReturnPinExecBytes.binary_correct_exec_proven holds for its 74"),
            "{}",
            v.summary
        );
        // already not verified (pruned): the counts are added
        let pruned = ok.replace("74 of 74 functions pass (0 dropped)", "71 of 74 functions pass (3 dropped)");
        let v = cover(verdict_of(&pruned, true, EXE), 74, "lean-link's region count");
        assert!(!v.verified);
        assert!(v.summary.starts_with("not verified: 3 of 74 Lean-compiled functions fail"), "{}", v.summary);
        assert!(v.summary.ends_with("; the binary check covers 71 function(s), the executable has 74 Lean-compiled function(s) (lean-link's region count)"), "{}", v.summary);
        // link-proof names functions of the executable it did not put in the bundle: not verified,
        // with its line, even when the counts would agree
        let gap = format!("cargo fv link-proof: {EXE}: 5 Lean-compiled function(s) of the executable (their __fvlean$ markers are in the link map) {NOT_IN_BUNDLE}: 1 unit(s): zerocopy-1.zerocopy.0-cgu.0.rcgu.o (5; its object is not in the link map); first: f\n{ok}");
        let v = cover(verdict_of(&gap, true, EXE), 74, "lean-link's region count");
        assert!(!v.verified);
        assert!(v.summary.starts_with(&format!("not verified: 5 Lean-compiled function(s) of the executable (their __fvlean$ markers are in the link map) {NOT_IN_BUNDLE}: 1 unit(s): zerocopy-1")), "{}", v.summary);
        assert!(v.summary.contains("; E2E.ReturnPinExecBytes.binary_correct_exec_proven holds for its 74 Lean-compiled functions"), "{}", v.summary);
    }
}
