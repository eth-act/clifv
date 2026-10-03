//! RUSTC_WRAPPER of `cargo fv` (and the linker rustc runs for member executables, recognised
//! by `FV_LINK_META` in the environment). See `cargo_fv::wrapper`. With `--keep-temps` it is
//! also the `lean-regalloc` that `lean-backend` runs (recognised by `FV_RA_REAL`): it runs the
//! real one and keeps a copy of its output (`cargo_fv::linkproof::regalloc_tee`).
fn main() {
    let argv: Vec<std::ffi::OsString> = std::env::args_os().skip(1).collect();
    if let Ok(real) = std::env::var(cargo_fv::linkproof::RA_REAL) {
        std::process::exit(cargo_fv::linkproof::regalloc_tee(&real, argv));
    }
    let code = match std::env::var("FV_LINK_META") {
        Ok(meta) => cargo_fv::wrapper::linker_main(&meta, argv),
        Err(_) => cargo_fv::wrapper::wrapper_main(argv),
    };
    std::process::exit(code);
}
