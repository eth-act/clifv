# CLIF opcode subset — `clif-subset-v1`

Pinned against Cranelift 0.136.1 (wasmtime v49.0.1). This is the named, versioned artifact
PLAN.md §3.3 requires. Two lists:

- **Emitter subset (E)**: the only opcodes `Compile.compile` may produce. Every E opcode must
  have (a) a `Clif.run` definition, (b) a VeriISLE CLIF spec in
  `cranelift/codegen/src/spec/inst_specs.isle`, where the "spec" column says yes, cross-read in
  `docs/contracts/clif-spec-crossread.md`, and (c) aarch64 lowering expansions covered by the
  default VeriISLE aarch64 run (`--default-excludes`) where possible (PLAN.md §6).
- **Semantics subset (S ⊇ E)**: what `Clif.run` implements so it can pass the upstream
  runtests. S may grow freely. E grows only by bumping this file's version.

Integer types in E: `i8 i16 i32 i64`. `i128` is in S but not in E, because the default
VeriISLE run excludes the `i128` tag. Floats and vectors are in neither list.

## E — emitter subset

| Opcode | VeriISLE spec | Emitter use / restriction |
| --- | --- | --- |
| `iconst` | yes | constants |
| `iadd` `isub` `ineg` `imul` | yes | wrapping `+% -% *%` |
| `umulhi` `smulhi` | yes | checked multiply (overflow iff high part ≠ 0 / ≠ sign fill) |
| `udiv` `urem` `sdiv` `srem` | yes | only behind an emitted zero-divisor guard (and a `MIN / -1` guard for signed). The emitter must prove the trap unreachable. |
| `band` `bor` `bxor` `bnot` | yes | bitwise |
| `ishl` `ushr` `sshr` `rotl` `rotr` | yes | shift amount masked mod width (CLIF semantics) |
| `clz` `ctz` `popcnt` | yes | intrinsics |
| `icmp` (all 10 `IntCC`) | yes | returns `i8` 0/1 |
| `uextend` `sextend` `ireduce` | yes | width changes |
| `load` `store` `uload8/16/32` `sload8/16/32` `istore8/16/32` | yes | flags: `notrap`/`aligned` only when justified (PLAN.md §3.2); little-endian |
| `stack_addr` | no | explicit stack slots for fixed-size aggregates |
| `jump` `brif` `br_table` `return` | no (terminators) | control flow |
| `call` | no | direct calls to other `flat def`s and to runtime externs, default call conv |
| `trap` | yes | **only** in provably unreachable positions (PLAN.md §3.2) |

Deliberately excluded from E:

- `uadd_overflow`, `sadd_overflow`, `usub_overflow`, `ssub_overflow`: no VeriISLE spec at the
  pin. Checked add/sub lowers as `iadd`/`isub` plus an `icmp` carry/borrow test, e.g.
  `c = icmp ult sum, a` for unsigned add.
- `select`: tagged `wasm_category_stack`, which `--default-excludes` skips. Use `brif` with
  block parameters.
- `trapz`, `trapnz`, `uadd_overflow_trap`: `throw` never lowers to a trap.
- `*_imm` forms: removed upstream.

## S — semantics subset (`Clif.run`)

E, plus: `i128` on all integer ops, `select`, `trapz`, `trapnz`, `uadd_overflow_trap`,
`uadd_overflow`, `sadd_overflow`, `usub_overflow`, `ssub_overflow`, `umul_overflow`,
`smul_overflow`, `bitrev`, `bswap`, `cls`, `iabs`, `smin` `smax` `umin` `umax`,
`uadd_sat` `sadd_sat` `usub_sat` `ssub_sat`, `bmask`, `iconcat` `isplit`, `nop`.
`stack_load`/`stack_store` do not exist in the 0.136.1 reader, so they are not in S.
M0 owns this list: extend it and record what was added and which filetests it unlocks in
`docs/contracts/clif.md`.

Added by M0 (see `docs/contracts/clif.md`, "S-list additions"): `select_spectre_guard`,
`bitselect`, `uadd_overflow_cin`, `sadd_overflow_cin`, `usub_overflow_bin`,
`ssub_overflow_bin`, `atomic_rmw` (all 11 operations), `atomic_cas`, `atomic_load`,
`atomic_store`, `fence`, `bitcast` (integer to integer of the same type), `return_call`.
