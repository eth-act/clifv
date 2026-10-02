//! `cargo fv build|run|test|report`: see docs/USAGE.md.
use cargo_fv::config::{Config, Mode};
use cargo_fv::report::{Report, UnitReport};
use cargo_fv::{TARGET, TOOLCHAIN};
use std::collections::HashSet;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const USAGE: &str = "\
usage: cargo fv <build|run|test> [--opt | --opt-proven-only] [--no-fallback] [--trap-replaced] [--keep-temps]
                                [--panic-abort] [--members-only] [cargo options] [-- args]
       cargo fv report [--functions] [--json] [--manifest-path PATH]

Builds for aarch64-unknown-linux-musl with rustc_codegen_cranelift; every function of every crate
compiled for the target (the workspace members and their dependencies; not std, which is
prebuilt, and not build scripts or proc macros, which run on the host) that the Lean backend
compiles runs the Lean backend's code, the rest keeps cg_clif's (fallback). Executables run
under qemu-aarch64-static. After a build the report is in target/fv-report.json (`cargo fv
report` prints it).

  --opt               run the Lean mid-end (all rules; nothing is reported verified)
  --opt-proven-only   run the Lean mid-end with the proven rules (E2E.backend_correct_opt_proven)
  --members-only      only the workspace members go through the Lean backend; dependencies are
                      plain cg_clif (separate target dir). Single dependencies: FV_SKIP_DEPS=a,b
                      or [package.metadata.fv] / [workspace.metadata.fv] skip-deps = [\"a\"]
  --no-fallback       fail unless every function of every workspace member runs Lean code
                      (dependencies may keep fallbacks; the report lists them)
  --trap-replaced     overwrite cg_clif's code of every Lean-compiled function (members and
                      dependencies) with traps (proof that the tests run the Lean code; separate
                      target dir)
  --keep-temps        keep the per-codegen-unit work directories (target/fv/<mode>/tmp)
  --panic-abort       build with -Cpanic=abort -Zpanic-abort-tests (default: panic=unwind, as cargo;
                      separate target dir)
  --functions         (report) list every function with its status and reason
  --json              (report) print target/fv-report.json";

fn die(msg: &str) -> ! {
    eprintln!("cargo fv: {msg}");
    std::process::exit(2)
}

fn which_tool(toolchain: &str, tool: &str) -> PathBuf {
    let out = Command::new("rustup")
        .args(["which", "--toolchain", toolchain, tool])
        .output()
        .unwrap_or_else(|e| die(&format!("rustup: {e}")));
    if !out.status.success() {
        die(&format!(
            "toolchain {toolchain} not found ({}); install it with\n  rustup toolchain install {toolchain} --component rustc-codegen-cranelift-preview --target {TARGET}",
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    PathBuf::from(String::from_utf8_lossy(&out.stdout).trim())
}

fn capture(cmd: &mut Command) -> String {
    let out = cmd.output().unwrap_or_else(|e| die(&format!("{:?}: {e}", cmd.get_program())));
    if !out.status.success() {
        die(&format!("{:?} failed: {}", cmd, String::from_utf8_lossy(&out.stderr).trim()));
    }
    String::from_utf8_lossy(&out.stdout).into_owned()
}

struct Meta {
    /// Manifest directories of the workspace members.
    members: Vec<PathBuf>,
    target: PathBuf,
    /// `[package.metadata.fv] skip = [...]`: (manifest dir, pattern).
    skip: Vec<(PathBuf, String)>,
    /// `[package.metadata.fv] skip-deps` of the members and `[workspace.metadata.fv] skip-deps`.
    skip_deps: Vec<String>,
}

fn str_list(v: &serde_json::Value) -> impl Iterator<Item = String> + '_ {
    v.as_array().into_iter().flatten().filter_map(|x| x.as_str().map(String::from))
}

/// `cargo metadata --no-deps`.
fn metadata(cargo: &Path, toolchain: &str, manifest: Option<&str>) -> Meta {
    let mut cmd = Command::new(cargo);
    cmd.env("RUSTUP_TOOLCHAIN", toolchain).args(["metadata", "--format-version", "1", "--no-deps"]);
    if let Some(m) = manifest {
        cmd.args(["--manifest-path", m]);
    }
    let v: serde_json::Value =
        serde_json::from_str(&capture(&mut cmd)).unwrap_or_else(|e| die(&format!("cargo metadata: {e}")));
    let ids: HashSet<String> = v["workspace_members"]
        .as_array()
        .map(|a| a.iter().filter_map(|x| x.as_str().map(String::from)).collect())
        .unwrap_or_default();
    let mut members = Vec::new();
    let mut skip = Vec::new();
    let mut skip_deps: Vec<String> = str_list(&v["metadata"]["fv"]["skip-deps"]).collect();
    for p in v["packages"].as_array().into_iter().flatten() {
        if ids.contains(p["id"].as_str().unwrap_or("")) {
            if let Some(m) = p["manifest_path"].as_str() {
                let d = Path::new(m).parent().unwrap_or(Path::new("/")).to_path_buf();
                let d = d.canonicalize().unwrap_or(d);
                for pat in str_list(&p["metadata"]["fv"]["skip"]) {
                    skip.push((d.clone(), pat));
                }
                skip_deps.extend(str_list(&p["metadata"]["fv"]["skip-deps"]));
                members.push(d);
            }
        }
    }
    let target = PathBuf::from(v["target_directory"].as_str().unwrap_or_else(|| die("cargo metadata: no target_directory")));
    skip_deps.sort();
    skip_deps.dedup();
    Meta { members, target, skip, skip_deps }
}

fn find_tool(env: &str, candidates: &[PathBuf]) -> PathBuf {
    if let Some(p) = std::env::var_os(env) {
        return PathBuf::from(p);
    }
    candidates
        .iter()
        .find(|p| p.exists())
        .cloned()
        .unwrap_or_else(|| die(&format!("none of {candidates:?} exists; set {env}")))
}

fn repo_root() -> PathBuf {
    let r = std::env::var_os("FV_ROOT")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../.."));
    let r = r.canonicalize().unwrap_or(r);
    for (p, how) in [
        (".lake/build/bin/lean-backend", "lake build lean-backend"),
        ("rust/target/release/clif-data-export", "cargo build --release -p clif-data-export (in rust/)"),
        ("rust/target/release/lean-regalloc", "cargo build --release -p lean-regalloc (in rust/)"),
        ("scripts/rust-clif/normalize.py", "a checkout of the repository"),
    ] {
        if !r.join(p).exists() {
            die(&format!("{} missing (FV_ROOT={}); build it: {how}", r.join(p).display(), r.display()));
        }
    }
    r
}

fn value_of(args: &[String], opt: &str) -> Option<String> {
    let mut it = args.iter();
    while let Some(a) = it.next() {
        if a == opt {
            return it.next().cloned();
        }
        if let Some(v) = a.strip_prefix(&format!("{opt}=")) {
            return Some(v.to_string());
        }
    }
    None
}

/// Everything that changes the Lean side of a build but not cargo's fingerprints.
fn stamp_of(cfg: &Config, wrapper: &Path, backend: &str) -> String {
    let mut s = String::new();
    for p in [cfg.lean_backend(), cfg.data_export(), cfg.lean_regalloc(), cfg.normalize(), wrapper.to_path_buf()] {
        let m = std::fs::metadata(&p).ok();
        s.push_str(&format!(
            "{} {} {:?}\n",
            p.display(),
            m.as_ref().map(|m| m.len()).unwrap_or(0),
            m.and_then(|m| m.modified().ok())
        ));
    }
    // the codegen backend (a rebuilt unwinding cg_clif at the same path must rebuild everything)
    let m = std::fs::metadata(backend).ok();
    s.push_str(&format!("backend {backend} {} {:?}\n", m.as_ref().map(|m| m.len()).unwrap_or(0), m.and_then(|m| m.modified().ok())));
    for k in ["FV_SKIP", "FV_ONLY"] {
        s.push_str(&format!("{k}={}\n", std::env::var(k).unwrap_or_default()));
    }
    for (d, p) in &cfg.pkg_skip {
        s.push_str(&format!("skip {} {p}\n", d.display()));
    }
    for p in &cfg.skip_deps {
        s.push_str(&format!("skip-dep {p}\n"));
    }
    s
}

fn report_path(target: &Path) -> PathBuf {
    target.join("fv-report.json")
}

fn cmd_report(args: &[String]) -> i32 {
    let toolchain = std::env::var("FV_TOOLCHAIN").unwrap_or(TOOLCHAIN.into());
    let cargo = which_tool(&toolchain, "cargo");
    let target = metadata(&cargo, &toolchain, value_of(args, "--manifest-path").as_deref()).target;
    let p = report_path(&target);
    let text = std::fs::read_to_string(&p).unwrap_or_else(|e| die(&format!("{}: {e} (run `cargo fv build` first)", p.display())));
    if args.iter().any(|a| a == "--json") {
        println!("{text}");
        return 0;
    }
    let r: Report = serde_json::from_str(&text).unwrap_or_else(|e| die(&format!("{}: {e}", p.display())));
    print!("{}", r.summary(args.iter().any(|a| a == "--functions")));
    0
}

fn main() {
    let mut argv: Vec<String> = std::env::args().skip(1).collect();
    if argv.first().map(String::as_str) == Some("fv") {
        argv.remove(0);
    }
    let Some(sub) = argv.first().cloned() else { die(USAGE) };
    let rest = argv[1..].to_vec();
    let code = match sub.as_str() {
        "build" | "run" | "test" => cmd_cargo(&sub, rest),
        "report" => cmd_report(&rest),
        "help" | "--help" | "-h" => {
            println!("{USAGE}");
            0
        }
        _ => die(&format!("unknown command `{sub}`\n{USAGE}")),
    };
    std::process::exit(code);
}

fn cmd_cargo(sub: &str, rest: Vec<String>) -> i32 {
    let (before, after): (Vec<String>, Vec<String>) = match rest.iter().position(|a| a == "--") {
        Some(i) => (rest[..i].to_vec(), rest[i + 1..].to_vec()),
        None => (rest, vec![]),
    };
    let mut mode = Mode::Plain;
    let mut no_fallback = false;
    let mut keep_temps = false;
    let mut trap_replaced = false;
    let mut panic_abort = false;
    let mut members_only = false;
    let mut cargo_args = Vec::new();
    for a in before {
        match a.as_str() {
            "--opt" => mode = Mode::Opt,
            "--opt-proven-only" => mode = Mode::OptProven,
            "--no-fallback" => no_fallback = true,
            "--keep-temps" => keep_temps = true,
            "--trap-replaced" => trap_replaced = true,
            "--panic-abort" => panic_abort = true,
            "--members-only" => members_only = true,
            _ => cargo_args.push(a),
        }
    }
    if value_of(&cargo_args, "--target").is_some() {
        die(&format!("cargo fv always builds for {TARGET}; drop --target"));
    }
    let profile = match value_of(&cargo_args, "--profile") {
        Some(p) if p == "dev" || p == "test" => "debug".to_string(),
        Some(p) if p == "bench" => "release".to_string(),
        Some(p) => p,
        None if cargo_args.iter().any(|a| a == "--release" || a == "-r") => "release".into(),
        None => "debug".into(),
    };

    let toolchain = std::env::var("FV_TOOLCHAIN").unwrap_or(TOOLCHAIN.into());
    let cargo = which_tool(&toolchain, "cargo");
    let rustc = which_tool(&toolchain, "rustc");
    let rustdoc = which_tool(&toolchain, "rustdoc");
    let root = repo_root();
    let Meta { members, target, skip: pkg_skip, mut skip_deps } =
        metadata(&cargo, &toolchain, value_of(&cargo_args, "--manifest-path").as_deref());
    let sysroot = PathBuf::from(capture(Command::new(&rustc).arg("--print").arg("sysroot")).trim());
    let host = capture(Command::new(&rustc).arg("-vV"))
        .lines()
        .find_map(|l| l.strip_prefix("host: ").map(String::from))
        .unwrap_or_else(|| die("rustc -vV: no host"));
    let bin = sysroot.join("lib/rustlib").join(&host).join("bin");
    // Codegen backend: with panic=unwind, cg_clif built with its `unwinding` feature (landing
    // pads: Drop during unwinding, catch_unwind) if available, else the shipped one (no landing
    // pads). With panic=abort the shipped one: the unwinding one would turn every call that may
    // unwind into a `try_call` with a terminate edge (rustc's abort_unwinding_calls), and those
    // functions would fall back.
    let unwinding_cg_clif = root.join("target/cg_clif-unwind/librustc_codegen_cranelift.so");
    let backend: String = match std::env::var("FV_CG_CLIF") {
        Ok(v) if v == "cranelift" => v,
        Ok(v) if Path::new(&v).exists() => v,
        Ok(v) => die(&format!("FV_CG_CLIF={v}: no such file (a cg_clif .so, or `cranelift` for the shipped one)")),
        Err(_) if !panic_abort && unwinding_cg_clif.exists() => unwinding_cg_clif.display().to_string(),
        Err(_) => "cranelift".into(),
    };
    let panic_desc = match (panic_abort, backend.as_str()) {
        (true, b) => format!("abort (cg_clif: {b})"),
        (false, "cranelift") => "unwind (shipped cg_clif: no landing pads, so no Drop during unwinding and catch_unwind in the crate does not catch)".to_string(),
        (false, b) => format!("unwind (cg_clif with unwinding: {b})"),
    };
    if !panic_abort && backend == "cranelift" {
        eprintln!("cargo fv: note: the shipped cg_clif has no landing pads (Drop during unwinding, catch_unwind in the crate); build the unwinding one with scripts/build-cg-clif-unwind.sh (docs/USAGE.md)");
    }
    // `FV_SKIP_DEPS=a,b`: more dependency packages that keep plain cg_clif
    skip_deps.extend(
        std::env::var("FV_SKIP_DEPS").unwrap_or_default().split([',', ' ']).filter(|s| !s.is_empty()).map(String::from),
    );
    skip_deps.sort();
    skip_deps.dedup();
    // one target dir per configuration that changes the objects (cargo does not see FV_*)
    let fv_dir = target.join("fv").join(format!(
        "{}{}{}{}",
        mode.name(),
        if members_only { "-members" } else { "" },
        if trap_replaced { "-trap" } else { "" },
        if panic_abort { "-abort" } else { "" }
    ));
    let cfg = Config {
        root,
        mode,
        members,
        members_only,
        skip_deps,
        report_dir: fv_dir.join("units"),
        tmp_dir: fv_dir.join("tmp"),
        rust_lld: find_tool("FV_RUST_LLD", &[bin.join("rust-lld")]),
        objcopy: find_tool("FV_OBJCOPY", &["/usr/lib/llvm-18/bin/llvm-objcopy".into(), bin.join("rust-objcopy")]),
        ar: find_tool("FV_AR", &["/usr/lib/llvm-18/bin/llvm-ar".into()]),
        python: std::env::var("FV_PYTHON").unwrap_or("python3".into()),
        jobs: std::env::var("FV_JOBS")
            .ok()
            .and_then(|j| j.parse().ok())
            .unwrap_or_else(|| std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4)),
        keep_temps,
        trap_replaced,
        pkg_skip,
    };
    let wrapper = std::env::current_exe()
        .ok()
        .and_then(|p| p.parent().map(|d| d.join("fv-rustc")))
        .filter(|p| p.exists())
        .unwrap_or_else(|| die("fv-rustc not found next to cargo-fv (build both: cargo build --release -p cargo-fv)"));

    // RUSTFLAGS for target crates (build scripts and proc macros are host crates: untouched)
    let mut flags: Vec<String> = match std::env::var("CARGO_ENCODED_RUSTFLAGS") {
        Ok(f) if !f.is_empty() => f.split('\x1f').map(String::from).collect(),
        _ => std::env::var("RUSTFLAGS").unwrap_or_default().split_whitespace().map(String::from).collect(),
    };
    flags.push(format!("-Zcodegen-backend={backend}"));
    let mut docflags: Vec<String> = std::env::var("RUSTDOCFLAGS").unwrap_or_default().split_whitespace().map(String::from).collect();
    if panic_abort {
        flags.extend(["-Cpanic=abort", "-Zpanic-abort-tests"].map(String::from));
        docflags.extend(["-Cpanic=abort", "-Zpanic-abort-tests"].map(String::from));
    }
    let runner_var = "CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUNNER";
    // The pinned toolchain's lib dir first: `cargo fv` itself may run under another toolchain's
    // rustup proxy (e.g. a rust-toolchain.toml above the crate), which put that toolchain's lib
    // dir in LD_LIBRARY_PATH; cargo adds the sysroot's rustlib/<host>/lib (holding a
    // librustc_driver when rustc-dev is installed) for build scripts, and a build script that
    // runs `$RUSTC` (libc, serde, …) then needs this toolchain's libLLVM.
    let ld_path = {
        let mut p = vec![sysroot.join("lib")];
        p.extend(std::env::var_os("LD_LIBRARY_PATH").map(|v| std::env::split_paths(&v).collect::<Vec<_>>()).unwrap_or_default());
        std::env::join_paths(p).unwrap_or_else(|e| die(&format!("LD_LIBRARY_PATH: {e}")))
    };
    let setup = |c: &mut Command| {
        c.env("LD_LIBRARY_PATH", &ld_path);
        c.env("RUSTUP_TOOLCHAIN", &toolchain)
            .env("RUSTC", &rustc)
            .env("RUSTDOC", &rustdoc)
            .env("RUSTC_WRAPPER", &wrapper)
            .env("CARGO_TARGET_DIR", &fv_dir)
            .env("CARGO_INCREMENTAL", "0")
            .env("CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_LINKER", &cfg.rust_lld)
            .env("CARGO_ENCODED_RUSTFLAGS", flags.join("\x1f"))
            .env_remove("RUSTFLAGS")
            .env("RUSTDOCFLAGS", docflags.join(" "))
            .envs(cfg.to_env());
        if std::env::var_os(runner_var).is_none() {
            c.env(runner_var, "qemu-aarch64-static");
        }
    };

    // cargo does not see the Lean tools or the FV settings: when they change, every unit we
    // compile (members and dependencies) is stale, so the profile's target-side output is
    // removed as a whole (host build scripts and proc macros live elsewhere and stay)
    let stamp_path = fv_dir.join(format!("fv-stamp.{profile}"));
    let stamp = stamp_of(&cfg, &wrapper, &backend);
    if std::fs::read_to_string(&stamp_path).ok().as_deref() != Some(stamp.as_str()) {
        let out = fv_dir.join(TARGET).join(&profile);
        if out.exists() {
            eprintln!("cargo fv: the Lean tools or the FV settings changed: rebuilding every target crate ({})", out.display());
            for d in [&out, &cfg.report_dir] {
                if let Err(e) = std::fs::remove_dir_all(d) {
                    if d.exists() {
                        die(&format!("{}: {e}", d.display()));
                    }
                }
            }
        }
        let _ = std::fs::create_dir_all(&fv_dir);
        let _ = std::fs::write(&stamp_path, &stamp);
    }

    // phase 1: build (artifact list from cargo's JSON messages)
    let build_sub = if sub == "test" { "test" } else { "build" };
    let mut b = Command::new(&cargo);
    b.arg(build_sub);
    let no_run = cargo_args.iter().any(|a| a == "--no-run");
    if sub == "test" && !no_run {
        b.arg("--no-run");
    }
    b.args(&cargo_args).args(["--target", TARGET, "--message-format=json-render-diagnostics"]);
    setup(&mut b);
    b.stdout(Stdio::piped()).stderr(Stdio::inherit());
    let out = b.output().unwrap_or_else(|e| die(&format!("{}: {e}", cargo.display())));
    // every target unit cargo reported (members and dependencies, fresh or rebuilt)
    let mut artifacts: HashSet<(u64, u64)> = HashSet::new();
    for line in String::from_utf8_lossy(&out.stdout).lines() {
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else { continue };
        if v["reason"] != "compiler-artifact" {
            continue;
        }
        let mut paths: Vec<&str> = v["filenames"].as_array().into_iter().flatten().filter_map(|f| f.as_str()).collect();
        paths.extend(v["executable"].as_str());
        for p in paths {
            if let Ok(m) = std::fs::metadata(p) {
                artifacts.insert((m.dev(), m.ino()));
            }
        }
    }
    let mut units: Vec<UnitReport> = Vec::new();
    if let Ok(rd) = std::fs::read_dir(&cfg.report_dir) {
        for e in rd.flatten() {
            let Ok(text) = std::fs::read_to_string(e.path()) else { continue };
            let Ok(u) = serde_json::from_str::<UnitReport>(&text) else { continue };
            if std::fs::metadata(&u.artifact).is_ok_and(|m| artifacts.contains(&(m.dev(), m.ino()))) {
                units.push(u);
            }
        }
    }
    // members first, then dependencies
    units.sort_by(|a, b| {
        (a.dep, &a.package, &a.crate_name, &a.kind, &a.src, &a.unit).cmp(&(b.dep, &b.package, &b.crate_name, &b.kind, &b.src, &b.unit))
    });
    let report = Report::new(&profile, mode.name(), mode.theorem().map(String::from), &panic_desc, units);
    let rp = report_path(&target);
    let _ = std::fs::write(&rp, serde_json::to_string_pretty(&report).expect("report serialises"));
    if !out.status.success() {
        return out.status.code().unwrap_or(1);
    }
    eprint!("{}", report.summary(false));
    let exes: Vec<usize> = report.units.iter().filter_map(|u| u.unit.binary.as_ref()).map(|b| b.lean_functions_linked).collect();
    let (m, d) = (&report.members, &report.deps);
    eprintln!(
        "cargo fv: {} of {} functions compiled by the Lean backend ({} verified): your crate(s) {} of {} ({} verified), dependencies {} of {} ({} verified); report: {}",
        report.totals.verified + report.totals.unverified,
        report.totals.functions,
        report.totals.verified,
        m.verified + m.unverified,
        m.functions,
        m.verified,
        d.verified + d.unverified,
        d.functions,
        d.verified,
        rp.display()
    );
    if !exes.is_empty() {
        eprintln!(
            "cargo fv: checked {} linked executable(s): {} function symbols in total resolve to Lean-compiled code (\"Lean in exe\", members and dependencies)",
            exes.len(),
            exes.iter().sum::<usize>()
        );
    }
    let mism = report.binary_mismatches();
    if !mism.is_empty() {
        for m in &mism {
            eprintln!("cargo fv: binary check failed: {m}");
        }
        return 1;
    }
    if no_fallback {
        // the members: dependencies keep the fallbacks the Lean backend cannot cover (floats,
        // SIMD, …); `cargo fv report` lists them with reasons
        let fb: Vec<_> = report.fallbacks().into_iter().filter(|(u, _)| !u.dep).collect();
        if !fb.is_empty() {
            eprintln!("cargo fv: --no-fallback: {} functions of the workspace members keep cg_clif's code:", fb.len());
            for (u, f) in fb.iter().take(30) {
                eprintln!("  {} ({}): {} — {}", u.crate_name, u.kind, f.instance, f.reason.as_deref().unwrap_or("?"));
            }
            return 1;
        }
        if !report.units.iter().any(|u| !u.unit.dep) {
            eprintln!("cargo fv: --no-fallback: no workspace member was compiled");
            return 1;
        }
    }
    if sub == "build" || no_run {
        return 0;
    }

    // phase 2: run (everything is fresh now)
    let mut r = Command::new(&cargo);
    r.arg(sub).args(&cargo_args).args(["--target", TARGET]);
    if !after.is_empty() {
        r.arg("--").args(&after);
    }
    setup(&mut r);
    match r.status() {
        Ok(s) => s.code().unwrap_or(1),
        Err(e) => die(&format!("{}: {e}", cargo.display())),
    }
}
