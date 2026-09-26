# Pinned external dependencies

Upgrading any of these is an explicit migration (PLAN.md §0). On a Cranelift bump, re-run
the `Clif.run` filetests, the VeriISLE cross-check and the differential corpus.

| Component | Pin | Notes |
| --- | --- | --- |
| Lean toolchain | `leanprover/lean4:v4.34.1` | `lean-toolchain` |
| Rust toolchain | `1.96.0` | `rust-toolchain.toml`; needed because Cranelift 0.136 has MSRV 1.96 |
| Cranelift crates | `=0.136.1` | `rust/Cargo.toml` workspace deps |
| Wasmtime source | tag `v49.0.1`, commit `46c23a87dac1465986a8ad53ba6a7ae49372857b` | `scripts/fetch-third-party.sh` puts it in `third_party/wasmtime`; Cranelift 0.136.1 ships in this release |
| Target triple | `aarch64-unknown-linux-gnu` semantics | Only the SysV AAPCS64 ABI. Native test executables are statically linked through Rust's `aarch64-unknown-linux-musl` target (with `rust-lld`) and run under `qemu-aarch64-static`, because this host has no aarch64 glibc sysroot. The generated code and its ABI are the same. |

## Why not Cranelift 0.130.2 (the version PLAN.md Appendix A was written against)

The VeriISLE specs PLAN.md relies on (`cranelift/codegen/src/spec/inst_specs.isle` and
`cranelift/codegen/src/isa/aarch64/spec/*.isle`, ASL-derived) first ship in wasmtime v47
(Cranelift 0.134). 0.130.2 (wasmtime v43) has only the older `veri_engine`. 0.136.1 is the
latest release at pin time (released 2026-09-24).

## Paths used from the pinned tree

- Filetests: `third_party/wasmtime/cranelift/filetests/filetests/runtests/*.clif`
- CLIF specs: `third_party/wasmtime/cranelift/codegen/src/spec/inst_specs.isle`
- aarch64 ASL-derived specs: `third_party/wasmtime/cranelift/codegen/src/isa/aarch64/spec/*.isle`
- aarch64 lowering rules: `third_party/wasmtime/cranelift/codegen/src/isa/aarch64/{lower,inst}.isle`
- Prelude: `third_party/wasmtime/cranelift/codegen/src/{prelude,prelude_lower}.isle`

## Syntax facts for 0.136.1 (checked against the pinned reader)

- There are no `*_imm` opcodes (`iadd_imm` and similar are gone). Use `iconst` plus the binary op.
- Trap codes are `stk_ovf heap_oob int_ovf int_divz bad_toint` and `user<N>`.
- `br_table v, blockD(args), [blockA(args), ...]`.
- Memory flags: `notrap aligned readonly little big can_move` plus trap-code flags.
