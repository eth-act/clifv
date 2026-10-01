# CLIF opcode subset — `clif-subset-v2`

## Changelog / Status

- **2026-10-02 (agent/atomics-proof stage B), E grows by `atomic_rmw` (all 11 operations) and
  `atomic_cas`**, i8–i64 little-endian (`Compile.instE`). Their root rules (2357–2377, 2390)
  are proven (`IselAtomic.lean`); the LL/SC loops are covered by one symbolic run of the loop
  body (`LoopRun.lean`, `RegLevelAtomic.lean`) on the single-threaded Arm model
  (`docs/decisions/arm-model.md`, "Atomics": `stlxr` succeeds and writes status 0).

- **2026-10-01 (agent/atomics-proof), E grows by `bmask`, `atomic_load`, `atomic_store` and
  `fence`** (`Compile.instE`; rows in the E table). `E2E.backend_correct_final` now covers
  functions with them: their root rules are proven (`FV/Backend/Proof/IselAtomic.lean`), and
  the register-level layer covers `csetm`, `dmb ish`, `ldar` and `stlr`
  (`RegallocAtomic.lean`, `MemRefines.lean`). This rests on the single-threaded Arm model
  (`docs/decisions/arm-model.md`, "Atomics"). `atomic_rmw` and `atomic_cas` (Cranelift's LL/SC
  loops) are still outside E. Their root rules are in the backend closure but proven vacuous:
  no instruction of `CtxInv` is outside E.

- **2026-10-01 (agent/indirect-proof), trusted-semantics growth of S**: `Clif.stepCallIndirect`
  (`call_indirect`, and `try_call_indirect` through it) whose callee address is no function of
  the program now calls the extern of the program at that address (`Clif.callExternAt`: the
  first extern some function of the program declares whose link-time `symbols` address is the
  callee value, run as `env.extern` with argument/result types checked against the call site's
  `sigN`, like `call`); it was stuck before. A callee that is a function of the program is
  entered as before. This is what `E2E.backend_correct_final` now covers for `call_indirect`,
  `func_addr` and `try_call_indirect` (`docs/contracts/e2e.md`, "Indirect calls").
  Effect on the differential tools: `scripts/clif-filetests.sh` 6072 pass / 7 fail / 13
  disagree, 0 printed files rejected — the documented 6070 / 7 / 13 plus the two runs of
  `runtests/try_call.clif` (both call `%call_i64`, a direct `try_call`); no runtest calls an
  extern indirectly, so no run and no agreement with the Cranelift interpreter changes.
  (Without `; data:` objects `Program.initMem` registers no function symbols, so `func_addr`
  stays stuck there, as before.) Under `clif-filetest --rust-env` with a data image,
  `func_addr` of `memset`, a vtable data object pointing at it, and a `try_call_indirect` of it
  now run (they were stuck), and the Lean backend's runs of the same file agree with
  Cranelift-native (`lean-backend-filetests.sh`, the Rust runtime linked).

- **2026-09-28 (M4Ctl3, contract change #9)**: `br_table` jump tables have fewer than `2^32`
  entries (`jump_table_size` is `u32`; the bounds check compares 32 bits); `lowerCheck`'s `brIdxOk`.
- **2026-09-27 (M4Ctl, contract change #6)**: `br_table` index restricted to at most 32 bits
  (see the terminator row below); enforced by the lowering validator, not by `Compile.functionE`.
- **v2 (2026-09-27)**: E gains `nop`, `symbol_value`, `select`, `smin`, `smax`, `umin`, `umax`,
  `bswap`, `bitrev`. Source: the rustc_codegen_cranelift survey
  (`docs/research/rust-clif-survey.md`, §2 and §7): with these nine, every function of the
  surveyed Rust categories (a)–(f) has all its opcodes in E (349/349 debug, 177/177 release).
  Work log, per-phase results and the backend plan: `docs/contracts/e-ext-v2.md`.
  - `Clif.run`: `symbol_value` is new (link-time image, `docs/contracts/clif.md`); the other
    eight were already in S, re-checked against `interpreter/src/step.rs`.
  - Spec cross-read: `bswap` and the four min/max have VeriISLE specs (theorems in
    `FVTest/Clif/SpecCrossread.lean`); `select`, `bitrev`, `nop`, `symbol_value` have none.
  - VeriISLE default run (tags, `docs/contracts/isle.md`): only `bswap`'s expansions are
    in it; `nop`/`symbol_value`/`select`/min-max expansions carry `TODO` (skipped by default),
    `bitrev` has no spec. E's criterion (c) is therefore not met for eight of the nine — the
    owner's decision to support cg_clif output overrides it; these rules need Lean proofs
    without a VeriISLE cross-check.
  - `Compile.onlySubsetE` (`FV/Compile/Subset.lean`) accepts v2.
- v1: initial list.

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
| `jump` `brif` `br_table` `return` | no (terminators) | control flow; `br_table`'s index must be `i8`/`i16`/`i32` (Cranelift's verifier requires `i32`; `Clif.run` does not check it). The lowering compares and dispatches on the low 32 bits, so M7's `lowerCheck` rejects an `i64` index (compile error; `BrIdxTyped`, contract change #6) |
| `call` | no | direct calls to other `flat def`s and to runtime externs, default call conv |
| `trap` | yes | **only** in provably unreachable positions (PLAN.md §3.2) |
| `nop` | no | v2: no effect (cg_clif comment anchors) |
| `select` | no (`inst_tags.isle` tags it, but its expansions are skipped via `TODO`) | v2: condition any of `i8..i64` (non-zero = true), values `i8..i64` |
| `smin` `smax` `umin` `umax` | yes | v2: `i8..i64` (`Ord::min`/`max`, `zip` lengths) |
| `bswap` | yes (i16/i32/i64) | v2: `i16 i32 i64` only (`bswap.i8` is not CLIF; `i128` excluded as everywhere) |
| `bitrev` | no | v2: `i8..i64` (`reverse_bits`) |
| `symbol_value` | no | v2: `symbol_value.i64 gvN` only, `gvN = symbol [colocated] %name[+offset]` naming a **data object** of the link-time image (`Clif.Image`); no `tls`, no function symbols, no other global-value kinds. Loads from it follow the `load` rules; stores into read-only objects are `stuck` (a precondition) |
| `tls_value` | no | v3 (agent/stack-tls-proof): `tls_value.i64 gvN`, `gvN = symbol [colocated] tls %name` (offset 0; the lowering rejects an offset). One thread: the address of the memory's symbol, as `symbol_value` (`Clif.run`); the backend's TLSDESC sequence under the trusted hook contract `TlsOk` (`docs/decisions/arm-model.md`) |
| `bmask` | no | v3 (agent/atomics-proof): result and operand `i8..i64` (Cranelift's `lower_bmask`: `cmp #0` + `csetm ne`, an `i8`/`i16` operand masked first) |
| `atomic_load` `atomic_store` | no | v3: `i8..i64`, little-endian, `i64` address (`ldar`/`stlr`). Single-threaded semantics: a plain load/store (`docs/decisions/arm-model.md`, "Atomics") |
| `fence` | no | v3: `dmb ish`, no effect in the single-threaded model |

Deliberately excluded from E:

- `uadd_overflow`, `sadd_overflow`, `usub_overflow`, `ssub_overflow`: no VeriISLE spec at the
  pin. Checked add/sub lowers as `iadd`/`isub` plus an `icmp` carry/borrow test, e.g.
  `c = icmp ult sum, a` for unsigned add.
- `trapz`, `trapnz`, `uadd_overflow_trap`: `throw` never lowers to a trap.
- `*_imm` forms: removed upstream.

## S — semantics subset (`Clif.run`)

E, plus: `i128` on all integer ops, `trapz`, `trapnz`, `uadd_overflow_trap`,
`uadd_overflow`, `sadd_overflow`, `usub_overflow`, `ssub_overflow`, `umul_overflow`,
`smul_overflow`, `cls`, `iabs`, `uadd_sat` `sadd_sat` `usub_sat` `ssub_sat`, `bmask`,
`iconcat` `isplit`. (`select`, min/max, `bswap`, `bitrev`, `nop` moved to E in v2.)
`stack_load`/`stack_store` do not exist in the 0.136.1 reader, so they are not in S.
M0 owns this list: extend it and record what was added and which filetests it unlocks in
`docs/contracts/clif.md`.

Added by M0 (see `docs/contracts/clif.md`, "S-list additions"): `select_spectre_guard`,
`bitselect`, `uadd_overflow_cin`, `sadd_overflow_cin`, `usub_overflow_bin`,
`ssub_overflow_bin`, `atomic_rmw` (all 11 operations), `atomic_cas`, `atomic_load`,
`atomic_store`, `fence`, `bitcast` (integer to integer of the same type), `return_call`.
