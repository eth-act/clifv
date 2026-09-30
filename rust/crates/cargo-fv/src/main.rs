//! `cargo fv build|run|test|report`: see docs/USAGE.md.
use cargo_fv::config::{Config, Mode};
use cargo_fv::report::{Report, UnitReport};
use cargo_fv::{TARGET, TOOLCHAIN};
use std::collections::HashSet;
use std::os::unix::fs::MetadataExt;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

const USAGE: &str = "\
usage: cargo fv <build|run|test> [--opt | --opt-proven-only] [--no-fallback] [--keep-temps] [cargo options] [-- args]
       cargo fv report [--functions] [--json] [--manifest-path PATH]

Builds for aarch64-unknown-linux-musl with rustc_codegen_cranelift; every function of the
workspace members that the Lean backend compiles runs the Lean backend's code, the rest keeps
cg_clif's (fallback). Executables run under qemu-aarch64-static. After a build the report is in
target/fv-report.json (`cargo fv report` prints it).

  --opt               run the Lean mid-end (all rules; nothing is reported verified)
  --opt-proven-only   run the Lean mid-end with the proven rules (E2E.backend_correct_opt_proven)
  --no-fallback       fail unless every function of every workspace member runs Lean code
  --keep-temps        keep the per-codegen-unit work directories (target/fv/<mode>/tmp)
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

/// `cargo metadata --no-deps`: (member manifest dirs, member package ids, target directory).
fn metadata(cargo: &Path, toolchain: &str, manifest: Option<&str>) -> (Vec<PathBuf>, HashSet<String>, PathBuf) {
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
    let mut dirs = Vec::new();
    for p in v["packages"].as_array().into_iter().flatten() {
        if ids.contains(p["id"].as_str().unwrap_or("")) {
            if let Some(m) = p["manifest_path"].as_str() {
                let d = Path::new(m).parent().unwrap_or(Path::new("/")).to_path_buf();
                dirs.push(d.canonicalize().unwrap_or(d));
            }
        }
    }
    let target = PathBuf::from(v["target_directory"].as_str().unwrap_or_else(|| die("cargo metadata: no target_directory")));
    (dirs, ids, target)
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

fn report_path(target: &Path) -> PathBuf {
    target.join("fv-report.json")
}

fn cmd_report(args: &[String]) -> i32 {
    let toolchain = std::env::var("FV_TOOLCHAIN").unwrap_or(TOOLCHAIN.into());
    let cargo = which_tool(&toolchain, "cargo");
    let (_, _, target) = metadata(&cargo, &toolchain, value_of(args, "--manifest-path").as_deref());
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
    let mut cargo_args = Vec::new();
    for a in before {
        match a.as_str() {
            "--opt" => mode = Mode::Opt,
            "--opt-proven-only" => mode = Mode::OptProven,
            "--no-fallback" => no_fallback = true,
            "--keep-temps" => keep_temps = true,
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
    let (members, member_ids, target) = metadata(&cargo, &toolchain, value_of(&cargo_args, "--manifest-path").as_deref());
    let sysroot = PathBuf::from(capture(Command::new(&rustc).arg("--print").arg("sysroot")).trim());
    let host = capture(Command::new(&rustc).arg("-vV"))
        .lines()
        .find_map(|l| l.strip_prefix("host: ").map(String::from))
        .unwrap_or_else(|| die("rustc -vV: no host"));
    let bin = sysroot.join("lib/rustlib").join(&host).join("bin");
    let fv_dir = target.join("fv").join(mode.name());
    let cfg = Config {
        root,
        mode,
        members,
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
    flags.extend(["-Zcodegen-backend=cranelift", "-Cpanic=abort", "-Zpanic-abort-tests"].map(String::from));
    let mut docflags: Vec<String> = std::env::var("RUSTDOCFLAGS").unwrap_or_default().split_whitespace().map(String::from).collect();
    docflags.extend(["-Cpanic=abort", "-Zpanic-abort-tests"].map(String::from));
    let runner_var = "CARGO_TARGET_AARCH64_UNKNOWN_LINUX_MUSL_RUNNER";
    let setup = |c: &mut Command| {
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

    // phase 1: build (artifact list from cargo's JSON messages)
    let build_sub = if sub == "test" { "test" } else { "build" };
    let mut b = Command::new(&cargo);
    b.arg(build_sub);
    if sub == "test" {
        b.arg("--no-run");
    }
    b.args(&cargo_args).args(["--target", TARGET, "--message-format=json-render-diagnostics"]);
    setup(&mut b);
    b.stdout(Stdio::piped()).stderr(Stdio::inherit());
    let out = b.output().unwrap_or_else(|e| die(&format!("{}: {e}", cargo.display())));
    let mut artifacts: HashSet<(u64, u64)> = HashSet::new();
    for line in String::from_utf8_lossy(&out.stdout).lines() {
        let Ok(v) = serde_json::from_str::<serde_json::Value>(line) else { continue };
        if v["reason"] != "compiler-artifact" || !member_ids.contains(v["package_id"].as_str().unwrap_or("")) {
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
    units.sort_by(|a, b| (&a.crate_name, &a.kind, &a.src, &a.unit).cmp(&(&b.crate_name, &b.kind, &b.src, &b.unit)));
    let report = Report::new(&profile, mode.name(), mode.theorem().map(String::from), units);
    let rp = report_path(&target);
    let _ = std::fs::write(&rp, serde_json::to_string_pretty(&report).expect("report serialises"));
    if !out.status.success() {
        return out.status.code().unwrap_or(1);
    }
    eprint!("{}", report.summary(false));
    let exes: Vec<usize> = report.units.iter().filter_map(|u| u.unit.binary.as_ref()).map(|b| b.lean_functions_linked).collect();
    eprintln!(
        "cargo fv: {} of {} functions compiled by the Lean backend ({} verified); report: {}",
        report.totals.verified + report.totals.unverified,
        report.totals.functions,
        report.totals.verified,
        rp.display()
    );
    if !exes.is_empty() {
        eprintln!(
            "cargo fv: checked {} linked executable(s): {} function symbols in total resolve to Lean-compiled code (\"Lean in exe\")",
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
        let fb = report.fallbacks();
        if !fb.is_empty() {
            eprintln!("cargo fv: --no-fallback: {} functions keep cg_clif's code:", fb.len());
            for (u, f) in fb.iter().take(30) {
                eprintln!("  {} ({}): {} — {}", u.crate_name, u.kind, f.instance, f.reason.as_deref().unwrap_or("?"));
            }
            return 1;
        }
        if report.units.is_empty() {
            eprintln!("cargo fv: --no-fallback: no workspace member was compiled");
            return 1;
        }
    }
    if sub == "build" {
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
