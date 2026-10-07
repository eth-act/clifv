//! `cargo fv`: build a Rust crate with the all-Lean CLIF → AArch64 backend.
//!
//! * `cargo-fv` (src/main.rs) runs cargo on the pinned nightly with rustc_codegen_cranelift
//!   (cg_clif), target `aarch64-unknown-linux-musl`, and `RUSTC_WRAPPER=fv-rustc`, then writes
//!   `target/fv-report.json` and prints a summary.
//! * `fv-rustc` (src/bin/fv-rustc.rs) is the wrapper: for every crate compiled for the target
//!   (workspace members and dependencies; not host crates) it makes cg_clif dump its CLIF, and
//!   recompiles every function of every codegen unit with the Lean backend ([`pipeline`]); for
//!   executables it is also the linker rustc runs ([`wrapper`]).
//! * `cargo fv link-proof` ([`linkproof`]): the input of the crate-level linking theorem from a
//!   `--keep-temps` build.
//! * the per-executable binary check of `cargo fv build` ([`bincheck`]): `link-proof` and
//!   `link-check` on every linked executable (`E2E.Binary.binary_correct`).
//! * `--lean-link` ([`leanlink`]): the Lean linker (`lake exe lean-link`) writes the program
//!   part of every executable.
//!
//! See docs/USAGE.md.
pub mod bincheck;
pub mod config;
pub mod leanlink;
pub mod linkproof;
pub mod pipeline;
pub mod report;
pub mod wrapper;

/// The only target: the Lean backend emits AArch64, musl gives static executables that run
/// under `qemu-aarch64-static` on this x86_64 host.
pub const TARGET: &str = "aarch64-unknown-linux-musl";

/// The nightly whose cg_clif the CLIF dumps come from (`docs/research/rust-route.md`).
pub const TOOLCHAIN: &str = "nightly-2026-09-26";
