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
}

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
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UnitReport {
    /// `<crate-name><extra-filename>`.
    pub unit: String,
    pub crate_name: String,
    pub package: String,
    /// `lib`, `bin`, `test`, …
    pub kind: String,
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
}

impl Counts {
    pub fn of(fs: &[FnReport]) -> Counts {
        let mut c = Counts::default();
        for f in fs {
            c.add(f.status);
        }
        c
    }
    fn add(&mut self, s: Status) {
        self.functions += 1;
        match s {
            Status::Verified => self.verified += 1,
            Status::Unverified => self.unverified += 1,
            Status::Fallback => self.fallback += 1,
        }
    }
    fn sum(&mut self, o: &Counts) {
        self.functions += o.functions;
        self.verified += o.verified;
        self.unverified += o.unverified;
        self.fallback += o.fallback;
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
    pub totals: Counts,
    pub units: Vec<UnitEntry>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UnitEntry {
    pub counts: Counts,
    #[serde(flatten)]
    pub unit: UnitReport,
}

impl Report {
    pub fn new(profile: &str, mode: &str, theorem: Option<String>, units: Vec<UnitReport>) -> Report {
        let mut totals = Counts::default();
        let units: Vec<UnitEntry> = units
            .into_iter()
            .map(|u| {
                let counts = Counts::of(&u.functions);
                totals.sum(&counts);
                UnitEntry { counts, unit: u }
            })
            .collect();
        Report {
            toolchain: crate::TOOLCHAIN.into(),
            target: crate::TARGET.into(),
            profile: profile.into(),
            mode: mode.into(),
            theorem,
            totals,
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
        let _ = writeln!(s, "  verified = compiled by the Lean backend and inside {th}");
        let _ = writeln!(
            s,
            "  {:<24} {:<6} {:>9} {:>9} {:>11} {:>9} {:>14}",
            "crate", "kind", "functions", "verified", "unverified", "fallback", "linked (Lean)"
        );
        for u in &self.units {
            let c = &u.counts;
            let linked = u.unit.binary.as_ref().map(|b| b.lean_functions_linked.to_string()).unwrap_or_default();
            let _ = writeln!(
                s,
                "  {:<24} {:<6} {:>9} {:>9} {:>11} {:>9} {:>14}",
                u.unit.crate_name, u.unit.kind, c.functions, c.verified, c.unverified, c.fallback, linked
            );
        }
        let t = &self.totals;
        let _ = writeln!(
            s,
            "  {:<24} {:<6} {:>9} {:>9} {:>11} {:>9}",
            "total", "", t.functions, t.verified, t.unverified, t.fallback
        );
        for (label, st) in [("unverified", Status::Unverified), ("fallback", Status::Fallback)] {
            let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
            for u in &self.units {
                for f in u.unit.functions.iter().filter(|f| f.status == st) {
                    *reasons.entry(generalize(f.reason.as_deref().unwrap_or("?"))).or_default() += 1;
                }
            }
            if reasons.is_empty() {
                continue;
            }
            let mut rs: Vec<_> = reasons.into_iter().collect();
            rs.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
            let _ = writeln!(s, "  {label} reasons:");
            for (r, n) in rs.iter().take(8) {
                let _ = writeln!(s, "    {n:>5}  {r}");
            }
            if rs.len() > 8 {
                let _ = writeln!(s, "    …{} more (target/fv-report.json)", rs.len() - 8);
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
                let _ = writeln!(s, "\n  {} ({}):", u.unit.crate_name, u.unit.kind);
                for f in &u.unit.functions {
                    let st = match f.status {
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

/// Group reasons: function and value names vary, the reason does not.
fn generalize(r: &str) -> String {
    let mut out = String::new();
    let mut chars = r.chars().peekable();
    while let Some(c) = chars.next() {
        if c == '%' {
            out.push_str("%X");
            while chars.peek().is_some_and(|c| c.is_alphanumeric() || *c == '_' || *c == '$' || *c == '.') {
                chars.next();
            }
        } else {
            out.push(c);
        }
    }
    out
}
