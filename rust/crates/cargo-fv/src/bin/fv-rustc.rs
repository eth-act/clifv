//! RUSTC_WRAPPER of `cargo fv` (and the linker rustc runs for member executables, recognised
//! by `FV_LINK_META` in the environment). See `cargo_fv::wrapper`.
fn main() {
    let argv: Vec<std::ffi::OsString> = std::env::args_os().skip(1).collect();
    let code = match std::env::var("FV_LINK_META") {
        Ok(meta) => cargo_fv::wrapper::linker_main(&meta, argv),
        Err(_) => cargo_fv::wrapper::wrapper_main(argv),
    };
    std::process::exit(code);
}
