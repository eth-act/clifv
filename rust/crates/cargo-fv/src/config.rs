//! Configuration shared by `cargo-fv` and `fv-rustc`, passed through `FV_*` environment
//! variables (cargo runs the wrapper; nothing else connects the two).
use std::path::{Path, PathBuf};

/// Which Lean pipeline compiles the functions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    /// Backend only: compiled functions outside `unverifiedReason?` are inside
    /// `E2E.backend_correct_final`.
    Plain,
    /// `--opt-proven-only`: the Lean mid-end with the proven rule set; the end-to-end theorem is
    /// `E2E.backend_correct_opt_proven`.
    OptProven,
    /// `--opt`: the Lean mid-end with every simplify rule, most of them unproven, so no
    /// function is reported verified.
    Opt,
}

impl Mode {
    pub fn name(self) -> &'static str {
        match self {
            Mode::Plain => "plain",
            Mode::OptProven => "opt-proven-only",
            Mode::Opt => "opt",
        }
    }
    pub fn parse(s: &str) -> Option<Mode> {
        match s {
            "plain" => Some(Mode::Plain),
            "opt-proven-only" => Some(Mode::OptProven),
            "opt" => Some(Mode::Opt),
            _ => None,
        }
    }
    /// Extra `lean-backend` arguments.
    pub fn backend_args(self) -> &'static [&'static str] {
        match self {
            Mode::Plain => &[],
            Mode::OptProven => &["--opt-proven-only"],
            Mode::Opt => &["--opt"],
        }
    }
    /// The theorem a "verified" function is inside.
    pub fn theorem(self) -> Option<&'static str> {
        match self {
            Mode::Plain => Some("E2E.backend_correct_final"),
            Mode::OptProven => Some("E2E.backend_correct_opt_proven"),
            Mode::Opt => None,
        }
    }
}

/// Everything the wrapper needs; `cargo-fv` fills it in, `fv-rustc` reads it back.
#[derive(Clone, Debug)]
pub struct Config {
    /// The repository root (lean-backend, clif-data-export, lean-regalloc, normalize.py).
    pub root: PathBuf,
    pub mode: Mode,
    /// `CARGO_MANIFEST_DIR`s of the workspace members.
    pub members: Vec<PathBuf>,
    /// `--members-only`: only the members are compiled by us (dependencies: plain cg_clif).
    /// Otherwise every crate compiled for the target is, except the packages in `skip_deps`.
    pub members_only: bool,
    /// Dependency packages that keep plain cg_clif (`package.metadata.fv.skip-deps`,
    /// `workspace.metadata.fv.skip-deps`, `FV_SKIP_DEPS`).
    pub skip_deps: Vec<String>,
    /// Per-unit reports (`<unit>.json`).
    pub report_dir: PathBuf,
    /// Scratch space (one directory per codegen unit, removed unless `keep_temps`).
    pub tmp_dir: PathBuf,
    pub rust_lld: PathBuf,
    pub objcopy: PathBuf,
    pub ar: PathBuf,
    pub python: String,
    /// `lean-backend` processes at a time, across all fv-rustc processes of the build.
    pub jobs: usize,
    pub keep_temps: bool,
    /// Keep what the per-executable binary check needs (`cargo fv link-proof`'s inputs: the
    /// compiled CLIF, the regalloc outputs, the link maps), without the objects; off with
    /// `--no-binary-check`.
    pub bin_check: bool,
    /// Overwrite cg_clif's replaced function bodies with traps (`--trap-replaced`).
    pub trap_replaced: bool,
    /// `--lean-link`: the Lean linker (`lake exe lean-link`, `Link.leanLink`) writes the
    /// program part of every executable: the Lean-compiled code is not merged into the codegen
    /// units but linked as one region (`.text.fvlean`), whose bytes the Lean linker computes.
    pub lean_link: bool,
    /// `[package.metadata.fv] skip = [...]` of the members: (manifest dir, pattern); matching
    /// functions keep cg_clif's code.
    pub pkg_skip: Vec<(PathBuf, String)>,
}

fn var(k: &str) -> Result<String, String> {
    std::env::var(k).map_err(|_| format!("{k} is not set (fv-rustc runs under `cargo fv`)"))
}

impl Config {
    pub fn lean_backend(&self) -> PathBuf {
        self.root.join(".lake/build/bin/lean-backend")
    }
    pub fn data_export(&self) -> PathBuf {
        self.root.join("rust/target/release/clif-data-export")
    }
    pub fn lean_regalloc(&self) -> PathBuf {
        self.root.join("rust/target/release/lean-regalloc")
    }
    pub fn normalize(&self) -> PathBuf {
        self.root.join("scripts/rust-clif/normalize.py")
    }

    /// Whether the inputs of `cargo fv link-proof` (and of the binary check) are kept.
    pub fn keep_link(&self) -> bool {
        self.keep_temps || self.bin_check
    }

    /// The environment `fv-rustc` reads.
    pub fn to_env(&self) -> Vec<(String, String)> {
        let members = self.members.iter().map(|p| p.display().to_string()).collect::<Vec<_>>().join("\n");
        vec![
            ("FV_ROOT".into(), self.root.display().to_string()),
            ("FV_MODE".into(), self.mode.name().into()),
            ("FV_MEMBERS".into(), members),
            ("FV_MEMBERS_ONLY".into(), if self.members_only { "1" } else { "0" }.into()),
            ("FV_DEP_SKIP".into(), self.skip_deps.join("\n")),
            ("FV_REPORT_DIR".into(), self.report_dir.display().to_string()),
            ("FV_TMP_DIR".into(), self.tmp_dir.display().to_string()),
            ("FV_RUST_LLD".into(), self.rust_lld.display().to_string()),
            ("FV_OBJCOPY".into(), self.objcopy.display().to_string()),
            ("FV_AR".into(), self.ar.display().to_string()),
            ("FV_PYTHON".into(), self.python.clone()),
            ("FV_JOBS".into(), self.jobs.to_string()),
            ("FV_KEEP_TEMPS".into(), if self.keep_temps { "1" } else { "0" }.into()),
            ("FV_BIN_CHECK".into(), if self.bin_check { "1" } else { "0" }.into()),
            ("FV_TRAP_REPLACED".into(), if self.trap_replaced { "1" } else { "0" }.into()),
            ("FV_LEAN_LINK".into(), if self.lean_link { "1" } else { "0" }.into()),
            (
                "FV_PKG_SKIP".into(),
                self.pkg_skip.iter().map(|(d, p)| format!("{}\t{p}", d.display())).collect::<Vec<_>>().join("\n"),
            ),
        ]
    }

    /// `None` when `FV_ROOT` is unset: fv-rustc was not started by `cargo fv`.
    pub fn from_env() -> Option<Result<Config, String>> {
        std::env::var_os("FV_ROOT")?;
        Some((|| {
            let mode = var("FV_MODE")?;
            Ok(Config {
                root: var("FV_ROOT")?.into(),
                mode: Mode::parse(&mode).ok_or(format!("FV_MODE: unknown mode {mode}"))?,
                members: var("FV_MEMBERS")?.lines().filter(|l| !l.is_empty()).map(PathBuf::from).collect(),
                members_only: var("FV_MEMBERS_ONLY")? == "1",
                skip_deps: var("FV_DEP_SKIP")?.lines().filter(|l| !l.is_empty()).map(String::from).collect(),
                report_dir: var("FV_REPORT_DIR")?.into(),
                tmp_dir: var("FV_TMP_DIR")?.into(),
                rust_lld: var("FV_RUST_LLD")?.into(),
                objcopy: var("FV_OBJCOPY")?.into(),
                ar: var("FV_AR")?.into(),
                python: var("FV_PYTHON")?,
                jobs: var("FV_JOBS")?.parse().map_err(|_| "FV_JOBS: not a number".to_string())?,
                keep_temps: var("FV_KEEP_TEMPS")? == "1",
                bin_check: var("FV_BIN_CHECK")? == "1",
                trap_replaced: var("FV_TRAP_REPLACED")? == "1",
                lean_link: var("FV_LEAN_LINK")? == "1",
                pkg_skip: var("FV_PKG_SKIP")?
                    .lines()
                    .filter_map(|l| l.split_once('\t').map(|(d, p)| (PathBuf::from(d), p.to_string())))
                    .collect(),
            })
        })())
    }

    /// The `package.metadata.fv.skip` patterns of the package being compiled.
    pub fn skip_patterns(&self) -> Vec<String> {
        let Some(dir) = std::env::var_os("CARGO_MANIFEST_DIR") else { return vec![] };
        let dir = Path::new(&dir).canonicalize().unwrap_or(PathBuf::from(&dir));
        self.pkg_skip.iter().filter(|(d, _)| *d == dir).map(|(_, p)| p.clone()).collect()
    }

    pub fn is_member(&self, manifest_dir: &Path) -> bool {
        let d = manifest_dir.canonicalize().unwrap_or(manifest_dir.to_path_buf());
        self.members.iter().any(|m| *m == d)
    }

    /// Whether a non-member package (by its Cargo package name) is compiled by us.
    pub fn compiles_dep(&self, package: &str) -> bool {
        !self.members_only && !self.skip_deps.iter().any(|s| s == package)
    }
}
