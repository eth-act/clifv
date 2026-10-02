//! Report types: one `UnitReport` per compiled crate unit (written by fv-rustc), aggregated by
//! `cargo fv` into `target/fv-report.json`.
use serde::{Deserialize, Serialize};
use std::collections::BTreeMap;
use std::fmt::Write as _;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Status {
    /// Compiled by the Lean backend, inside the end-to-end theorem of the mode.
    Verified,
    /// Compiled by the Lean backend, outside the theorem (reason given).
    Unverified,
    /// Not compiled by us: cg_clif's code is used (reason given).
    Fallback,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct FnReport {
    /// The linker symbol (hashed mangling).
    pub symbol: String,
    /// The Rust item, from cg_clif's `; instance` comment.
    pub instance: String,
    pub status: Status,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    /// A verified function with a `try_call`: the theorem covers its normal returns; the
    /// unwinding path (landing pads, LSDA) is trusted.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub normal_returns: bool,
}

/// The label of a verified function with a `try_call`.
pub const NORMAL_RETURNS: &str = "verified (normal returns; unwinding trusted)";

/// Result of checking a linked executable: every function whose Lean code we merged into an
/// object carries a local marker symbol `__fvlean$<symbol>` at the start of our code; in the
/// linked binary, `<symbol>` must have the marker's address.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct BinaryCheck {
    pub path: String,
    /// Symbols resolved to Lean-compiled code in the executable (all crates' markers).
    pub lean_functions_linked: usize,
    /// Markers whose function symbol has another address (cg_clif's code won: a bug).
    pub mismatches: Vec<String>,
    /// Set when the check could not run (e.g. a stripped binary).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
    /// Where the executable's functions come from (from the link map).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub origin: Option<ExeOrigin>,
}

/// The function symbols of a linked executable (distinct addresses), by origin.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ExeOrigin {
    pub functions: usize,
    /// Lean-compiled code (a marker at the address), of a workspace member / a dependency.
    pub lean_members: usize,
    pub lean_deps: usize,
    /// Functions of crates we compiled that run cg_clif's code (fallbacks).
    pub cg_clif: usize,
    /// Not compiled by us, prebuilt (the sysroot): std/core/alloc, compiler_builtins, musl libc.
    pub prebuilt: usize,
    /// Not compiled by us, other inputs: crates outside the scope (`--members-only`,
    /// skip-deps), linker-synthesised code.
    pub other: usize,
    /// Lean-compiled functions per package (`<package>` or `<package> (dep)`).
    pub lean_by_package: BTreeMap<String, usize>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UnitReport {
    /// `<crate-name><extra-filename>`.
    pub unit: String,
    pub crate_name: String,
    pub package: String,
    /// `lib`, `bin`, `test`, …
    pub kind: String,
    /// The crate root rustc compiled (as cargo passed it, e.g. `src/lib.rs`, `tests/t.rs`).
    #[serde(default)]
    pub src: String,
    /// Not a workspace member: a dependency (registry, git or path package).
    #[serde(default)]
    pub dep: bool,
    /// The output rustc wrote (rlib or executable), for matching cargo's artifact messages.
    pub artifact: String,
    pub mode: String,
    pub theorem: Option<String>,
    /// Codegen units whose pipeline failed as a whole (every function falls back).
    #[serde(default)]
    pub cgu_errors: Vec<String>,
    pub functions: Vec<FnReport>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub binary: Option<BinaryCheck>,
}

#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct Counts {
    pub functions: usize,
    pub verified: usize,
    pub unverified: usize,
    pub fallback: usize,
    /// Of `verified`: functions with a `try_call` (`NORMAL_RETURNS`).
    #[serde(default)]
    pub verified_normal_returns: usize,
}

impl Counts {
    pub fn of(fs: &[FnReport]) -> Counts {
        let mut c = Counts::default();
        for f in fs {
            c.add(f);
        }
        c
    }
    fn add(&mut self, f: &FnReport) {
        self.functions += 1;
        match f.status {
            Status::Verified => {
                self.verified += 1;
                if f.normal_returns {
                    self.verified_normal_returns += 1;
                }
            }
            Status::Unverified => self.unverified += 1,
            Status::Fallback => self.fallback += 1,
        }
    }
    fn sum(&mut self, o: &Counts) {
        self.functions += o.functions;
        self.verified += o.verified;
        self.unverified += o.unverified;
        self.fallback += o.fallback;
        self.verified_normal_returns += o.verified_normal_returns;
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Report {
    pub toolchain: String,
    pub target: String,
    pub profile: String,
    pub mode: String,
    /// The theorem "verified" refers to (none with `--opt`).
    pub theorem: Option<String>,
    /// Panic strategy and codegen backend, e.g. `unwind (cg_clif with unwinding: …)`.
    #[serde(default)]
    pub panic: String,
    pub totals: Counts,
    /// Of `totals`: the workspace members' units ("your crate(s)") and the dependencies'.
    #[serde(default)]
    pub members: Counts,
    #[serde(default)]
    pub deps: Counts,
    pub units: Vec<UnitEntry>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UnitEntry {
    pub counts: Counts,
    #[serde(flatten)]
    pub unit: UnitReport,
}

impl Report {
    pub fn new(profile: &str, mode: &str, theorem: Option<String>, panic: &str, units: Vec<UnitReport>) -> Report {
        let mut totals = Counts::default();
        let mut members = Counts::default();
        let mut deps = Counts::default();
        let units: Vec<UnitEntry> = units
            .into_iter()
            .map(|u| {
                let counts = Counts::of(&u.functions);
                totals.sum(&counts);
                if u.dep { &mut deps } else { &mut members }.sum(&counts);
                UnitEntry { counts, unit: u }
            })
            .collect();
        Report {
            toolchain: crate::TOOLCHAIN.into(),
            target: crate::TARGET.into(),
            profile: profile.into(),
            mode: mode.into(),
            theorem,
            panic: panic.into(),
            totals,
            members,
            deps,
            units,
        }
    }

    pub fn fallbacks(&self) -> Vec<(&UnitReport, &FnReport)> {
        self.units
            .iter()
            .flat_map(|u| u.unit.functions.iter().filter(|f| f.status == Status::Fallback).map(move |f| (&u.unit, f)))
            .collect()
    }

    pub fn binary_mismatches(&self) -> Vec<String> {
        self.units
            .iter()
            .filter_map(|u| u.unit.binary.as_ref())
            .flat_map(|b| b.mismatches.iter().map(move |m| format!("{}: {m}", b.path)))
            .collect()
    }

    /// Human summary; `functions` lists every function.
    pub fn summary(&self, functions: bool) -> String {
        let mut s = String::new();
        let th = self.theorem.as_deref().unwrap_or("none: --opt runs unproven mid-end rules");
        let _ = writeln!(s, "cargo fv report — {} {} profile, mode {}", self.target, self.profile, self.mode);
        if !self.panic.is_empty() {
            let _ = writeln!(s, "  panic={}", self.panic);
        }
        let _ = writeln!(s, "  verified = compiled by the Lean backend and inside {th}");
        let row = |s: &mut String, pkg: &str, kind: &str, root: &str, c: &Counts, linked: &str| {
            let _ = writeln!(
                s,
                "  {:<22} {:<5} {:<22} {:>9} {:>9} {:>10} {:>9} {:>13}",
                pkg, kind, root, c.functions, c.verified, c.unverified, c.fallback, linked
            );
        };
        let _ = writeln!(
            s,
            "  {:<22} {:<5} {:<22} {:>9} {:>9} {:>10} {:>9} {:>13}",
            "package", "kind", "crate root", "functions", "verified", "unverified", "fallback", "Lean in exe"
        );
        for u in &self.units {
            let linked = u.unit.binary.as_ref().map(|b| b.lean_functions_linked.to_string()).unwrap_or_default();
            // a dependency's library: kind `dep`
            let kind = if u.unit.dep { "dep" } else { u.unit.kind.as_str() };
            row(&mut s, &u.unit.package, kind, short_root(&u.unit.src), &u.counts, &linked);
        }
        row(&mut s, "your crate(s)", "", "", &self.members, "");
        row(&mut s, "dependencies", "", "", &self.deps, "");
        row(&mut s, "total", "", "", &self.totals, "");
        let _ = writeln!(s, "  std (not compiled by us: prebuilt std/core/alloc rlibs, plus compiler_builtins and musl libc)");
        let t = &self.totals;
        if t.verified_normal_returns > 0 {
            let _ = writeln!(
                s,
                "  of the verified: {} {NORMAL_RETURNS}: functions with a try_call, the theorem \
                 covers their normal returns; landing pads and the LSDA are trusted",
                t.verified_normal_returns
            );
        }
        for u in &self.units {
            let Some(o) = u.unit.binary.as_ref().and_then(|b| b.origin.as_ref()) else { continue };
            let deps: Vec<String> =
                o.lean_by_package.iter().filter(|(p, _)| p.ends_with(" (dep)")).map(|(p, n)| format!("{} {n}", p.trim_end_matches(" (dep)"))).collect();
            let _ = writeln!(
                s,
                "  exe {} ({} {}): {} functions: Lean {} (your crate(s) {}, dependencies {}), cg_clif fallback {}, std (prebuilt) {}, other not compiled by us {}",
                u.unit.package,
                u.unit.kind,
                short_root(&u.unit.src),
                o.functions,
                o.lean_members + o.lean_deps,
                o.lean_members,
                o.lean_deps,
                o.cg_clif,
                o.prebuilt,
                o.other
            );
            if !deps.is_empty() {
                let _ = writeln!(s, "    Lean in exe per dependency: {}", deps.join(", "));
            }
        }
        for (group, dep) in [("your crate(s)", false), ("dependencies", true)] {
            for (label, st) in [("unverified", Status::Unverified), ("fallback", Status::Fallback)] {
                let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
                for u in self.units.iter().filter(|u| u.unit.dep == dep) {
                    for f in u.unit.functions.iter().filter(|f| f.status == st) {
                        *reasons.entry(generalize(f.reason.as_deref().unwrap_or("?"))).or_default() += 1;
                    }
                }
                if reasons.is_empty() {
                    continue;
                }
                let mut rs: Vec<_> = reasons.into_iter().collect();
                rs.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
                let _ = writeln!(s, "  {label} reasons ({group}):");
                let shown = if functions { rs.len() } else { 8 };
                for (r, n) in rs.iter().take(shown) {
                    let _ = writeln!(s, "    {n:>5}  {r}");
                }
                if rs.len() > shown {
                    let _ = writeln!(s, "    …{} more (cargo fv report --functions)", rs.len() - shown);
                }
            }
        }
        for u in &self.units {
            for e in &u.unit.cgu_errors {
                let _ = writeln!(s, "  {} ({}): codegen unit fell back entirely: {e}", u.unit.crate_name, u.unit.kind);
            }
            if let Some(b) = &u.unit.binary {
                if let Some(n) = &b.note {
                    let _ = writeln!(s, "  {}: binary check: {n}", b.path);
                }
                for m in &b.mismatches {
                    let _ = writeln!(s, "  {}: BINARY CHECK FAILED: {m}", b.path);
                }
            }
        }
        if functions {
            for u in &self.units {
                let _ = writeln!(s, "\n  {} ({} {}):", u.unit.crate_name, u.unit.kind, u.unit.src);
                for f in &u.unit.functions {
                    let st = match f.status {
                        Status::Verified if f.normal_returns => NORMAL_RETURNS,
                        Status::Verified => "verified",
                        Status::Unverified => "unverified",
                        Status::Fallback => "fallback",
                    };
                    let r = f.reason.as_deref().map(|r| format!(" ({r})")).unwrap_or_default();
                    let _ = writeln!(s, "    {st:<10} {}{r}", f.instance);
                }
            }
        }
        s
    }
}

/// A crate root outside the package (`../../x.rs`): just the file name; an absolute one (a
/// registry or git dependency): the path inside the package (`src/lib.rs`).
fn short_root(src: &str) -> &str {
    if src.starts_with('/') {
        let mut ends = src.rmatch_indices('/').map(|(i, _)| i);
        return match (ends.next(), ends.next()) {
            (Some(_), Some(i)) => &src[i + 1..],
            _ => src,
        };
    }
    if src.contains("../") { src.rsplit('/').next().unwrap_or(src) } else { src }
}

/// Group reasons: function names (`%f`), value names (`v12`) and measured sizes (numbers of 5
/// or more digits, e.g. the validation budget's cost) vary, the reason does not.
fn generalize(r: &str) -> String {
    let mut out = String::new();
    let mut chars = r.chars().peekable();
    let mut prev: Option<char> = None;
    while let Some(c) = chars.next() {
        let at_word_start = !prev.is_some_and(|p| p.is_alphanumeric() || p == '_');
        if c == '%' {
            out.push_str("%X");
            while chars.peek().is_some_and(|c| c.is_alphanumeric() || *c == '_' || *c == '$' || *c == '.') {
                chars.next();
            }
        } else if c == 'v' && at_word_start && chars.peek().is_some_and(|d| d.is_ascii_digit()) {
            let mut digits = String::new();
            while let Some(d) = chars.peek().filter(|d| d.is_ascii_digit()) {
                digits.push(*d);
                chars.next();
            }
            if chars.peek().is_some_and(|n| n.is_alphanumeric() || *n == '_') {
                out.push('v');
                out.push_str(&digits);
            } else {
                out.push_str("vN");
            }
        } else if c.is_ascii_digit() && at_word_start {
            let mut digits = String::from(c);
            while let Some(d) = chars.peek().filter(|d| d.is_ascii_digit()) {
                digits.push(*d);
                chars.next();
            }
            out.push_str(if digits.len() >= 5 { "N" } else { &digits });
        } else {
            out.push(c);
        }
        prev = out.chars().last();
    }
    out
}
