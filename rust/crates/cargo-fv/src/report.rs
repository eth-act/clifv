//! Report types: one `UnitReport` per compiled crate unit (written by fv-rustc), aggregated by
//! `cargo fv` into `target/fv-report.json`.
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Status {
    /// Compiled by the Lean backend, inside the per-function theorem lean-backend named
    /// (`theorem`), every checkable premise of which it decided.
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
    /// A verified function with a `try_call` whose unwinding is not covered (lean-backend's
    /// `compiled, verified for normal returns` line: the unwinding theorem's checks failed or do
    /// not apply): the theorem covers its normal returns; the unwinding path is trusted. A
    /// `try_call` function passing the checks is plainly verified.
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub normal_returns: bool,
    /// A verified function's theorem (lean-backend's verdict, `FVTest/Backend/FnVerdict.lean`):
    /// its fully qualified name, with the pass it composes (`(T := …)`) where there is one.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub theorem: Option<String>,
    /// What the theorem is about: `the source function`, or the compiled function after the
    /// transformations it does not compose (the `i128` legalisation, constant-phi removal, the
    /// mid-end, Cranelift's optimiser for an `.opt.clif` retry).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub about: Option<String>,
    /// A Lean-compiled function compiled from its `.unopt.clif` (not the `.opt.clif` retry)
    /// while cg_clif optimised it: Cranelift's `opt_level` in the dump's header, when it is not
    /// `none` (`--release`, or a profile raising `opt-level`). Stock compiles Cranelift's
    /// optimised function; the theorem is about the unoptimised one (#1119).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub unopt_input_opt_level: Option<String>,
    /// `cargo fv --midval` (#1119): what lean-backend's mid-end validator did for a function
    /// cg_clif optimised.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub midval: Option<MidvalReport>,
}

/// What `lean-backend --midval-opt` did for one function (#1119).
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MidvalReport {
    /// `validated`: Cranelift's optimised function was compiled, `Opt.MidVal.checkCertC`
    /// decided, and a verified one's theorem (`E2E.backend_correct_midval_*`) is about the
    /// `.unopt.clif` ([`MIDVAL_ABOUT`]); `validated-link`: compiled from the optimised function
    /// too, accepted by the validator's hoisting mode (`Link.hoistCopy`), its theorem about the
    /// optimised function and carried to the `.unopt.clif` at link level (link-check's `…_midS`,
    /// lean-link's `…MidS`); `rejected` (the check failed), `not composed` (no theorem
    /// through the validator for the optimised function) or `not attempted`: compiled from the
    /// `.unopt.clif` exactly as without `--midval`.
    pub outcome: String,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
    /// Cranelift's `opt_level` in the dump's header.
    pub opt_level: String,
}

/// What a theorem through the mid-end validator is about (`FVTest.Backend.FnVerdict.midAbout`).
pub const MIDVAL_ABOUT: &str =
    "the source function (.unopt.clif), compiled from cg_clif's optimised dump validated by Opt.MidVal";

impl FnReport {
    /// The key the summary counts a verified function under: the theorem, `about the compiled
    /// function` when it is not about the source function, and the normal-returns label.
    pub fn theorem_key(&self) -> String {
        let t = self.theorem.as_deref().unwrap_or("no theorem named");
        let about = match self.about.as_deref() {
            Some(a) if a != "the source function" && a != MIDVAL_ABOUT => " (about the compiled function)",
            _ => "",
        };
        let nr = if self.normal_returns { " [normal returns only; unwinding trusted]" } else { "" };
        format!("{t}{about}{nr}")
    }

    /// Compiled from Cranelift's optimised function validated by `Opt.MidVal` (`--midval`).
    pub fn midval_validated(&self) -> bool {
        self.midval.as_ref().is_some_and(|m| m.outcome == "validated")
    }

    /// Compiled from Cranelift's optimised function accepted by `Opt.MidVal`'s hoisting mode, its
    /// premise decided at link level (`--midval`, `validated-link`).
    pub fn midval_validated_link(&self) -> bool {
        self.midval.as_ref().is_some_and(|m| m.outcome == "validated-link")
    }
}

/// The label of a verified function with a `try_call` whose unwinding is not covered.
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
    /// `--lean-link`: the theorems covering the executable the Lean linker wrote (`lake exe
    /// lean-link`'s `coverage:`; `none (…)` for the bare-linker fallback outside `--verified`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lean_link: Option<String>,
    /// `--lean-link`: the number of functions in the region the Lean linker wrote (`lean-link`'s
    /// count: its `N function(s), … written by` line).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub lean_link_region: Option<usize>,
    /// The binary check after the build (`cargo fv link-proof` + `link-check`; not run with
    /// `--no-binary-check`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub bin_check: Option<BinCheckVerdict>,
}

/// The binary check of one executable (docs/contracts/e2e.md, "Binary level (M9)"; #1130).
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct BinCheckVerdict {
    /// The Lean-compiled functions of the executable, which the theorem must cover: with
    /// `--lean-link` lean-link's region count (`lean_link_region`), else the markers resolved in
    /// the executable (`lean_functions_linked`).
    pub functions: usize,
    /// Which of the two counts `functions` is.
    pub functions_from: String,
    /// The functions the theorem `link-check` names covers (its program's passing functions);
    /// none when it names no theorem.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub checked: Option<usize>,
    /// The theorem covers every Lean-compiled function of the executable (`checked` =
    /// `functions`) and every check holds.
    pub verified: bool,
    /// cargo fv's line for the executable.
    pub summary: String,
}

/// The function symbols of a linked executable (distinct addresses), by origin.
#[derive(Clone, Debug, Default, Serialize, Deserialize)]
pub struct ExeOrigin {
    pub functions: usize,
    /// Lean-compiled code (a marker at the address), of a workspace member / a dependency / the
    /// standard library (`--build-std`).
    pub lean_members: usize,
    pub lean_deps: usize,
    #[serde(default)]
    pub lean_std: usize,
    /// Functions of crates we compiled that run cg_clif's code (fallbacks).
    pub cg_clif: usize,
    /// Not compiled by us: the prebuilt sysroot (std/core/alloc, compiler_builtins, musl libc
    /// and its crt objects); with `--build-std` compiler_builtins (LLVM) and musl libc.
    pub prebuilt: usize,
    /// Not compiled by us, other inputs: crates outside the scope (`--members-only`,
    /// skip-deps), linker-synthesised code.
    pub other: usize,
    /// Lean-compiled functions per package (`<package>`, `<package> (dep)` or `<package> (std)`).
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
    /// Not a workspace member: a dependency (registry, git or path package) or a crate of the
    /// standard library.
    #[serde(default)]
    pub dep: bool,
    /// A crate of the standard library built by `cargo fv --build-std` (`-Zbuild-std`).
    #[serde(default)]
    pub std: bool,
    /// The output rustc wrote (rlib or executable), for matching cargo's artifact messages.
    pub artifact: String,
    pub mode: String,
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
    /// Of `verified`: per theorem (`FnReport::theorem_key`), how many functions.
    #[serde(default)]
    pub by_theorem: BTreeMap<String, usize>,
    /// Of `verified` + `unverified`: compiled from the `.unopt.clif` while cg_clif optimised the
    /// function (`FnReport::unopt_input_opt_level`, #1119).
    #[serde(default)]
    pub unopt_input_optimised: usize,
    /// Of `verified` + `unverified`: compiled from Cranelift's optimised function validated by
    /// `Opt.MidVal` (`--midval`, #1119; `FnReport::midval`).
    #[serde(default)]
    pub midval_validated: usize,
    /// Of `verified` + `unverified`: compiled from Cranelift's optimised function accepted by the
    /// validator's hoisting mode (`FnReport::midval_validated_link`).
    #[serde(default)]
    pub midval_validated_link: usize,
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
                *self.by_theorem.entry(f.theorem_key()).or_default() += 1;
            }
            Status::Unverified => self.unverified += 1,
            Status::Fallback => {
                self.fallback += 1;
                return;
            }
        }
        if f.unopt_input_opt_level.is_some() {
            self.unopt_input_optimised += 1;
        }
        if f.midval_validated() {
            self.midval_validated += 1;
        }
        if f.midval_validated_link() {
            self.midval_validated_link += 1;
        }
    }
    fn sum(&mut self, o: &Counts) {
        self.functions += o.functions;
        self.verified += o.verified;
        self.unverified += o.unverified;
        self.fallback += o.fallback;
        self.verified_normal_returns += o.verified_normal_returns;
        self.unopt_input_optimised += o.unopt_input_optimised;
        self.midval_validated += o.midval_validated;
        self.midval_validated_link += o.midval_validated_link;
        for (t, n) in &o.by_theorem {
            *self.by_theorem.entry(t.clone()).or_default() += n;
        }
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Report {
    pub toolchain: String,
    pub target: String,
    pub profile: String,
    pub mode: String,
    /// Panic strategy and codegen backend, e.g. `unwind (cg_clif with unwinding: …)`.
    #[serde(default)]
    pub panic: String,
    pub totals: Counts,
    /// Of `totals`: the workspace members' units ("your crate(s)"), the dependencies' and, with
    /// `--build-std`, the standard library's.
    #[serde(default)]
    pub members: Counts,
    #[serde(default)]
    pub deps: Counts,
    #[serde(default)]
    pub std: Counts,
    pub units: Vec<UnitEntry>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct UnitEntry {
    pub counts: Counts,
    #[serde(flatten)]
    pub unit: UnitReport,
}

impl Report {
    pub fn new(profile: &str, mode: &str, panic: &str, units: Vec<UnitReport>) -> Report {
        let mut totals = Counts::default();
        let mut members = Counts::default();
        let mut deps = Counts::default();
        let mut std = Counts::default();
        let units: Vec<UnitEntry> = units
            .into_iter()
            .map(|u| {
                let counts = Counts::of(&u.functions);
                totals.sum(&counts);
                if u.std {
                    &mut std
                } else if u.dep {
                    &mut deps
                } else {
                    &mut members
                }
                .sum(&counts);
                UnitEntry { counts, unit: u }
            })
            .collect();
        Report {
            toolchain: crate::TOOLCHAIN.into(),
            target: crate::TARGET.into(),
            profile: profile.into(),
            mode: mode.into(),
            panic: panic.into(),
            totals,
            members,
            deps,
            std,
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

    /// #1119: cargo fv's line about the Lean-compiled functions cg_clif optimised (the dumps'
    /// header, so a profile raising `opt-level` counts as `--release` does): how many were compiled
    /// from cg_clif's unoptimised CLIF and, with `--midval`, how many from Cranelift's optimised
    /// function validated by `Opt.MidVal`; `None` when there is none.
    pub fn unopt_input_note(&self) -> Option<String> {
        let t = &self.totals;
        if t.unopt_input_optimised == 0 && t.midval_validated == 0 && t.midval_validated_link == 0 {
            return None;
        }
        let levels: BTreeSet<&str> = self
            .units
            .iter()
            .flat_map(|u| u.unit.functions.iter())
            .filter(|f| f.status != Status::Fallback)
            .filter_map(|f| {
                f.unopt_input_opt_level
                    .as_deref()
                    .or(f.midval.as_ref().filter(|m| m.outcome == "validated" || m.outcome == "validated-link").map(|m| m.opt_level.as_str()))
            })
            .collect();
        let levels = levels.into_iter().collect::<Vec<_>>().join(", ");
        if t.midval_validated == 0 && t.midval_validated_link == 0 {
            return Some(format!(
                "{} of the {} Lean-compiled functions were compiled from cg_clif's unoptimised CLIF (.unopt.clif) while cg_clif \
                 optimised them (opt_level={} in their dumps' header): a verified one's theorem is about the unoptimised \
                 function, Cranelift's mid-end is neither applied to it nor trusted, and stock compiles Cranelift's optimised \
                 function, so the code is in general not byte-equal to stock's (docs/USAGE.md \"Optimised builds\", #1119)",
                t.unopt_input_optimised,
                t.verified + t.unverified,
                levels
            ));
        }
        let link = if t.midval_validated_link == 0 {
            String::new()
        } else {
            format!(
                "; {} more were accepted by its hoisting mode (lean-backend decided Link.hoistCopy: Cranelift hoisted a \
                 symbol_value, tls_value or func_addr out of a loop) and compiled from Cranelift's optimised function: a \
                 verified one's theorem is about the optimised function, and link-check's …_midS and lean-link's …MidS \
                 theorems, where named, are about the unoptimised one at the executable's symbol table",
                t.midval_validated_link
            )
        };
        Some(format!(
            "of the {} Lean-compiled functions cg_clif optimised (opt_level={} in their dumps' header), {} were validated by \
             the mid-end validator (lean-backend decided Opt.MidVal.checkCertC) and compiled from Cranelift's optimised \
             function: a verified one's theorem (E2E.backend_correct_midval_*) is about the unoptimised function \
             (.unopt.clif) and Cranelift's mid-end is not trusted{}; {} were compiled from cg_clif's unoptimised CLIF \
             (.unopt.clif), with a theorem about it and code in general not byte-equal to stock's (docs/USAGE.md \
             \"Optimised builds\", #1119)",
            t.midval_validated + t.midval_validated_link + t.unopt_input_optimised,
            levels,
            t.midval_validated,
            link,
            t.unopt_input_optimised
        ))
    }

    /// Human summary; `functions` lists every function.
    pub fn summary(&self, functions: bool) -> String {
        let mut s = String::new();
        let _ = writeln!(s, "cargo fv report — {} {} profile, mode {}", self.target, self.profile, self.mode);
        if !self.panic.is_empty() {
            let _ = writeln!(s, "  panic={}", self.panic);
        }
        let _ = writeln!(
            s,
            "  verified = compiled by the Lean backend inside the per-function theorem lean-backend names, \
             every checkable premise of which it decided on the code it emitted (run and environment \
             hypotheses stay premises: docs/contracts/e2e.md); per theorem below"
        );
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
            // a dependency's library: kind `dep`; a crate of the standard library: `std`
            let kind = if u.unit.std {
                "std"
            } else if u.unit.dep {
                "dep"
            } else {
                u.unit.kind.as_str()
            };
            row(&mut s, &u.unit.package, kind, short_root(&u.unit.src), &u.counts, &linked);
        }
        let built_std = self.units.iter().any(|u| u.unit.std);
        row(&mut s, "your crate(s)", "", "", &self.members, "");
        row(&mut s, "dependencies", "", "", &self.deps, "");
        if built_std {
            row(&mut s, "std (--build-std)", "", "", &self.std, "");
        }
        row(&mut s, "total", "", "", &self.totals, "");
        if built_std {
            let _ = writeln!(s, "  not compiled by us: compiler_builtins (LLVM) and musl libc");
        } else {
            let _ = writeln!(s, "  std (not compiled by us: prebuilt std/core/alloc rlibs, plus compiler_builtins and musl libc)");
        }
        let t = &self.totals;
        if !t.by_theorem.is_empty() {
            let _ = writeln!(s, "  verified functions by theorem:");
            for (th, n) in &t.by_theorem {
                let _ = writeln!(s, "    {n:>7}  {th}");
            }
        }
        // #1119 `--midval`: the validator's outcomes over the functions it was asked about
        let mut mid: BTreeMap<String, usize> = BTreeMap::new();
        for f in self.units.iter().flat_map(|u| u.unit.functions.iter()) {
            if let Some(m) = &f.midval {
                let key = match &m.reason {
                    Some(r) if m.outcome != "validated" => format!("{}: {}", m.outcome, generalize(r)),
                    _ => m.outcome.clone(),
                };
                *mid.entry(key).or_default() += 1;
            }
        }
        if !mid.is_empty() {
            let mut ms: Vec<_> = mid.into_iter().collect();
            ms.sort_by(|a, b| b.1.cmp(&a.1).then(a.0.cmp(&b.0)));
            let _ = writeln!(s, "  mid-end validator (--midval, #1119), per function cg_clif optimised:");
            let shown = if functions { ms.len() } else { 12 };
            for (k, n) in ms.iter().take(shown) {
                let _ = writeln!(s, "    {n:>7}  {k}");
            }
            if ms.len() > shown {
                let _ = writeln!(s, "    …{} more (cargo fv report --functions)", ms.len() - shown);
            }
        }
        if t.verified_normal_returns > 0 {
            let _ = writeln!(
                s,
                "  of the verified: {} {NORMAL_RETURNS}: functions with a try_call, the theorem \
                 covers their normal returns only; landing pads and the LSDA are trusted",
                t.verified_normal_returns
            );
        }
        for u in &self.units {
            let Some(o) = u.unit.binary.as_ref().and_then(|b| b.origin.as_ref()) else { continue };
            let per = |suffix: &str| -> Vec<String> {
                o.lean_by_package.iter().filter(|(p, _)| p.ends_with(suffix)).map(|(p, n)| format!("{} {n}", p.trim_end_matches(suffix))).collect()
            };
            let (deps, std) = (per(" (dep)"), per(" (std)"));
            let _ = writeln!(
                s,
                "  exe {} ({} {}): {} functions: Lean {} (your crate(s) {}, dependencies {}, std {}), cg_clif fallback {}, prebuilt or LLVM (std unless --build-std, compiler_builtins, musl libc) {}, other not compiled by us {}",
                u.unit.package,
                u.unit.kind,
                short_root(&u.unit.src),
                o.functions,
                o.lean_members + o.lean_deps + o.lean_std,
                o.lean_members,
                o.lean_deps,
                o.lean_std,
                o.cg_clif,
                o.prebuilt,
                o.other
            );
            if !deps.is_empty() {
                let _ = writeln!(s, "    Lean in exe per dependency: {}", deps.join(", "));
            }
            if !std.is_empty() {
                let _ = writeln!(s, "    Lean in exe per std crate: {}", std.join(", "));
            }
        }
        for (group, dep, std) in [("your crate(s)", false, false), ("dependencies", true, false), ("std", true, true)] {
            for (label, st) in [("unverified", Status::Unverified), ("fallback", Status::Fallback)] {
                let mut reasons: BTreeMap<String, usize> = BTreeMap::new();
                for u in self.units.iter().filter(|u| u.unit.dep == dep && u.unit.std == std) {
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
                    let r = match (&f.reason, &f.theorem) {
                        (Some(r), _) => format!(" ({r})"),
                        (None, Some(t)) => {
                            format!(" ({t}; about {})", f.about.as_deref().unwrap_or("the source function"))
                        }
                        (None, None) => String::new(),
                    };
                    let m = match &f.midval {
                        Some(MidvalReport { outcome, reason: Some(why), .. }) => format!(" [midval: {outcome}: {why}]"),
                        Some(MidvalReport { outcome, reason: None, .. }) => format!(" [midval: {outcome}]"),
                        None => String::new(),
                    };
                    let _ = writeln!(s, "    {st:<10} {}{r}{m}", f.instance);
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

#[cfg(test)]
mod tests {
    use super::*;

    fn f(status: Status, theorem: Option<&str>, about: Option<&str>, normal: bool) -> FnReport {
        FnReport {
            symbol: "s".into(),
            instance: "i".into(),
            status,
            reason: None,
            normal_returns: normal,
            theorem: theorem.map(String::from),
            about: about.map(String::from),
            unopt_input_opt_level: None,
            midval: None,
        }
    }

    fn unit(dep: bool, functions: Vec<FnReport>) -> UnitReport {
        UnitReport {
            unit: "u".into(),
            crate_name: "c".into(),
            package: "p".into(),
            kind: "lib".into(),
            src: "src/lib.rs".into(),
            dep,
            std: false,
            artifact: "a".into(),
            mode: "plain".into(),
            cgu_errors: vec![],
            functions,
            binary: None,
        }
    }

    /// #1119: functions compiled from the `.unopt.clif` while cg_clif optimised them are counted
    /// (of the Lean-compiled ones) and named in one line; a build without them has no line and
    /// writes no per-function field.
    #[test]
    fn unopt_input_of_optimised_functions() {
        let th = Some("E2E.backend_correct_world_niX_semantic_return_pins");
        let opt = |mut r: FnReport| {
            r.unopt_input_opt_level = Some("speed_and_size".into());
            r
        };
        let members = vec![
            opt(f(Status::Verified, th, Some("the source function"), false)),
            opt(f(Status::Verified, th, Some("the source function"), false)),
            opt(f(Status::Unverified, None, None, false)),
            // the `.opt.clif` retry: compiled from Cranelift's optimised function
            f(Status::Verified, th, Some("the source function, compiled from cg_clif's optimised dump (.opt.clif)"), false),
            // cg_clif's code: not counted, whatever the field says
            opt(f(Status::Fallback, None, None, false)),
        ];
        let deps = vec![opt(f(Status::Verified, th, Some("the source function"), false)), f(Status::Fallback, None, None, false)];
        let r = Report::new("release", "plain", "", vec![unit(false, members), unit(true, deps)]);
        assert_eq!((r.totals.unopt_input_optimised, r.members.unopt_input_optimised, r.deps.unopt_input_optimised), (4, 3, 1));
        // nothing else changes: the counts are the ones without the field
        assert_eq!((r.totals.functions, r.totals.verified, r.totals.unverified, r.totals.fallback), (7, 4, 1, 2));
        let note = r.unopt_input_note().expect("a line");
        assert!(note.starts_with("4 of the 5 Lean-compiled functions were compiled from cg_clif's unoptimised CLIF"), "{note}");
        assert!(note.contains("(opt_level=speed_and_size in their dumps' header)") && note.ends_with("#1119)"), "{note}");
        let json = serde_json::to_value(&r).unwrap();
        assert_eq!(json["totals"]["unopt_input_optimised"], 4);

        // a build at opt_level=none: no line, no per-function field, the count 0
        let plain = Report::new("debug", "plain", "", vec![unit(false, vec![f(Status::Verified, th, Some("the source function"), false)])]);
        assert!(plain.unopt_input_note().is_none());
        let json = serde_json::to_value(&plain).unwrap();
        assert_eq!(json["totals"]["unopt_input_optimised"], 0);
        assert!(json["units"][0]["functions"][0].get("unopt_input_opt_level").is_none());
        // reports written before the field read as 0
        let mut old = json.clone();
        old["totals"].as_object_mut().unwrap().remove("unopt_input_optimised");
        let old: Report = serde_json::from_value(old).unwrap();
        assert_eq!(old.totals.unopt_input_optimised, 0);
    }

    /// #1119 `--midval`: validated functions are counted, keyed by their own theorem (about the
    /// source function), and the line says how many of the optimised functions each way.
    #[test]
    fn midval_validated_functions() {
        let th = Some("E2E.backend_correct_world_niX_semantic_return_pins");
        let mth = Some("E2E.backend_correct_midval_semantic_return_pins");
        let mid = |mut r: FnReport, outcome: &str, why: Option<&str>| {
            r.midval = Some(MidvalReport {
                outcome: outcome.into(),
                reason: why.map(String::from),
                opt_level: "speed_and_size".into(),
            });
            if outcome != "validated" && outcome != "validated-link" {
                r.unopt_input_opt_level = Some("speed_and_size".into());
            }
            r
        };
        let fs = vec![
            mid(f(Status::Verified, mth, Some(MIDVAL_ABOUT), false), "validated", None),
            mid(f(Status::Verified, mth, Some(MIDVAL_ABOUT), false), "validated", None),
            mid(f(Status::Verified, th, Some("the source function"), false), "rejected", Some("Opt.MidVal.check rejects: rewrite:operand")),
            mid(f(Status::Fallback, None, None, false), "validated", None),
            mid(f(Status::Verified, th, Some("Cranelift's optimised function (.opt.clif)"), false), "validated-link", None),
        ];
        let r = Report::new("release", "plain", "", vec![unit(false, fs)]);
        assert_eq!((r.totals.midval_validated, r.totals.unopt_input_optimised, r.totals.verified), (2, 1, 4));
        assert_eq!(r.totals.midval_validated_link, 1);
        assert_eq!(r.totals.by_theorem.get(mth.unwrap()), Some(&2));
        let note = r.unopt_input_note().expect("a line");
        assert!(note.starts_with("of the 4 Lean-compiled functions cg_clif optimised (opt_level=speed_and_size"), "{note}");
        assert!(note.contains(", 2 were validated by the mid-end validator") && note.contains("; 1 were compiled from"), "{note}");
        assert!(note.contains("; 1 more were accepted by its hoisting mode"), "{note}");
        let s = r.summary(false);
        assert!(s.contains("mid-end validator (--midval, #1119)"), "{s}");
        let json = serde_json::to_value(&r).unwrap();
        assert_eq!(json["totals"]["midval_validated"], 2);
        assert_eq!(json["units"][0]["functions"][2]["midval"]["outcome"], "rejected");
    }

    #[test]
    fn counts_per_theorem() {
        let r = "E2E.backend_correct_world_niX_semantic_return_pins";
        let c = Counts::of(&[
            f(Status::Verified, Some(r), Some("the source function"), false),
            f(Status::Verified, Some(r), Some("the compiled function, after the i128 legalisation (not composed on this path)"), false),
            f(Status::Verified, Some("E2E.backend_correct_final_cleanup"), Some("the source function"), true),
            f(Status::Unverified, None, None, false),
        ]);
        assert_eq!(c.verified, 3);
        assert_eq!(c.verified_normal_returns, 1);
        assert_eq!(c.by_theorem.get(r), Some(&1));
        assert_eq!(c.by_theorem.get(&format!("{r} (about the compiled function)")), Some(&1));
        assert_eq!(
            c.by_theorem.get("E2E.backend_correct_final_cleanup [normal returns only; unwinding trusted]"),
            Some(&1)
        );
        // the per-theorem counts add up to the verified count
        assert_eq!(c.by_theorem.values().sum::<usize>(), c.verified);
    }
}
