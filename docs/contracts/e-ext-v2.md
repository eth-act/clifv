# Emitter subset extension `clif-subset-v2` (cg_clif step 1)

Branch `agent/e-ext-v2`. Goal: add `nop`, `symbol_value`, `select`, `smin`, `smax`, `umin`,
`umax`, `bswap`, `bitrev` to E (source: `docs/research/rust-clif-survey.md`) end to end,
differentially tested; proofs later.

## Status

- [x] Phase 1 (CLIF side, spec cross-read, ISLE closure, Arm model, native path) — done.
- [x] Phase 2 (Lean backend) — done (2026-09-27); results below, plan kept for reference.

## Phase 2 results (2026-09-27)

| Item | Result |
| --- | --- |
| Isel | 9 opcodes → `InstructionData` (`NullAry Nop`, `UnaryGlobalValue SymbolValue`, `Ternary Select`, `Binary Smin…Umax`, `Unary Bswap/Bitrev`); externs `invalid_reg`, `value_array_3` (ctor + extractor), `symbol_value_data` added to the backend.md transcription table; `nop`'s `invalid_reg` output dropped (`lower.rs:953`) |
| MInst / regalloc operands | `MInst.csel` (`def rd; use rn; use rm`, `mod.rs:453`); `LoadExtNameGot` (`def rd`) reused for data symbols |
| Encoder / printer | standalone `csel`; `BitOp.rev32` at 32 bits = `rev wd, wn`; GOT relocations against undefined `STT_NOTYPE` data symbols |
| e-v2 fixtures (360 runs) | Lean backend native 360/360 pass, 360/360 agree with Cranelift-native, both `--regalloc regalloc2` and `stack`, and `--asm`; `Clif.run` 360/360 |
| Runtests | **3085 pass** / 0 fail / 0 disagree (was 2791), 53 files fully E (+`arithmetic`, `bitrev`, `integer-minmax`, `issue-5498`, `issue5839`), 12 partly (`select` 147/175, `bswap` 13/14); corpus 114/114, extrt 22/22; same for both allocators |
| `lean-backend-encode-check.sh` | 971/971 functions byte-identical (both allocators); e-v2 fixtures 52/52 |
| `lean-backend-regalloc-test` | 932/932 accepted by the Lean checker; all mutants rejected |
| Rust survey (nop kept) | cg_clif corpus **760 / 933** (was 368 with nop dropped), core+alloc **267 / 1575** (was 228); smoke 88/88; details `docs/research/rust-clif-survey.md` §5 "Post-v2" |

## Phase 1 results (2026-09-27)

| Item | Result |
| --- | --- |
| `docs/contracts/clif-subset.md` | `clif-subset-v2`: the 9 opcodes in E with restrictions; changelog |
| `Clif.run` semantics re-check vs `interpreter/src/step.rs` | `select` (`into_bool` = non-zero), `smin/smax/umin/umax`, `bswap` (`swap_bytes`), `bitrev` (`reverse_bits`), `nop` (`Continue`) agree; `symbol_value` new |
| Link-time data model | `Program.data : List DataObject`, `DataItem.byte/addr`, `Mem.symbols`, read-only `Alloc`s, `Image.mem`, `Program.initMem`; `run` starts from `initMem` (`run_of_data_nil`: unchanged without data); `; data:` directives parsed/printed (round trip) |
| Fixtures `FVTest/Clif/fixtures/e-v2-*.clif` | `select` 85 runs (cond × value types i8..i64 + saturating add), min/max 160 (4 ops × 4 widths × 10), `bswap` 27 (i16/i32/i64), `bitrev` 36 (i8..i64), `nop` 24, `symbol_value` 28 — **360 runs** |
| `Clif.run` vs expectations | 360/360 pass, round trip 0 failures, printed files accepted by `clif-oracle check` |
| `Clif.run` vs Cranelift interpreter | 332/332 agree; the 28 `symbol_value` runs are `oracle-error` (interpreter: `GlobalValueData::Symbol => unimplemented!()`) |
| `Clif.run` vs native Cranelift (`clif-native`) | **360/360 agree** (all six files, incl. the 28 `symbol_value` runs) |
| Full `scripts/clif-filetests.sh` | 6070 pass / 7 fail / 13 disagree — the documented baseline (5706 + 360 new + 4 `parse-aliases-gv`), no new failures |
| `lake exe compile-diff` | 107/107, `onlySubsetE` 41/41 (`FV/Compile/Subset.lean` now v2) |
| Spec cross-read | `bswap_i16/_i32/_i64` (transcribed `bswap16!/32!/64!` macros, `bv_decide`), `smin_i8 … umax_i64`; no spec: `select`, `bitrev`, `nop`, `symbol_value` |
| ISLE closure | 392 → **442 rules** (+50, of which 17 roots), 488 → 536 terms, 119 → **128 extern terms** (+9, 1 with spec); details and VeriISLE coverage in `docs/contracts/isle.md` |
| VeriISLE default run | only `bswap` expansions in it; `nop`, `symbol_value`, `select`, min/max skipped via `TODO` tags; `bitrev` has no spec |
| Arm model | emitted forms: `csel` (x), `cmp` (reg/extended), `tst`, `sxtb/h`, `uxtb/h`, `rev16 w`, `rev w`, `rev x`, `rbit w/x`, `lsr #imm`, `adrp` + `ldr` (GOT), `mov`/`add`; all already decoded/executed (REV family from LNSym). New cosim specs `rev16`, `rev (32)`, `rev32`, `rev (64)`: 200/0 each, 1000/0 at seed 12345; full cosim 165 forms / 33000 vectors / 0 failures |
| Native data | `clif2obj`: `gvN = symbol %x` → imported data symbol; `clif-native`: `; data:` → `data.s` → linked; `cargo test -p clif-native` 3/3 (new `data_objects_from_directives`, incl. read-only store → SIGSEGV) |

Decisions (owner away, conservative):
- Data objects live in the filetest text as `; data:` comments, so one file drives `Clif.run`,
  cranelift-reader (ignores comments) and native. Real cg_clif data needs a manifest from the
  frontend (survey §8, P4); the directive format is the natural target for such a manifest.
- Read-only data is enforced in `Clif.run` (store → `stuck`) because native code faults there.
- `symbol_value` is in E only at `i64` and only for data objects; function addresses
  (`func_addr`, vtables of `fn` pointers) stay out.

## Phase 2 plan (Lean backend), to run after `agent/regalloc2` is merged

1. `git merge main`; rebuild; re-run `scripts/lean-backend-filetests.sh` baseline.
2. **Isel (`FV/Backend/Isel.lean`)**, instruction → `InstructionData` values:
   - `nop` → `NullAry(Opcode.Nop)`; root rule `lower.isle:78` returns `invalid_reg`: model the
     extern `invalid_reg` (a distinguished invalid `Reg`) and make the driver accept a
     `lower` result for an instruction with no results (Cranelift ignores it). Emits nothing.
   - `select ty c x y` → `Ternary(Opcode.Select, value_array_3 c x y)`; externs
     `value_array_3` (`pack/unpack_value_array_3`). Root `lower.isle:2267` →
     `lower_select ty (is_nonzero_cmp cond)` → `lower_select_cond` rule 1
     (`inst.isle:5364`: `with_flags flags (csel cond rn rm)`); `ty_scalar_float`, `ty_vec64`,
     `ty_vec128` extractors must return `fail` at integer types (higher-priority arms).
   - `smin/smax/umin/umax` → `Binary(Opcode.Smin…)`; roots `lower.isle:1222–1228`
     (`ty_int`, `emit_icmp`, `lower_select`); vector roots excluded by `ty_vec*`,
     `not_i64x2`, `multi_lane`, `dynamic_lane` failing.
   - `bswap` → `Unary(Opcode.Bswap)`; roots `2035/2038/2041` → `a64_rev16/32/64` → `bit_rr`.
   - `bitrev` → `Unary(Opcode.Bitrev)`; roots `1931/1937` (`rbit.32` + `lsr_imm`), `1946`.
   - `symbol_value` → `UnaryGlobalValue(Opcode.SymbolValue, gv)`; extractor
     `symbol_value_data gv` = `(ExternalName, RelocDistance, offset)` from the function's
     `globals` (`.symbol n off colocated` → distance `Near` iff colocated); `box_external_name`
     exists; `load_ext_name` with `is_pic = true` → `LoadExtNameGot` (+ `add` of `imm` if
     offset ≠ 0, `inst.isle:3983–3988`). Opcode checks: accept these in `eTy`/opcode tables
     (`bswap` only i16..i64).
3. **MInst (`FV/Backend/MInst.lean`)**: add `CSel { rd, rn, rm, cond }` (value decoder
   `"CSel"`); regalloc operands as `aarch64_get_operands` (`mod.rs:453`): `def rd`, `use rn`,
   `use rm`. `LoadExtNameGot`: `def rd` (`mod.rs:926`). `BitRR` exists (`def rd`, `use rn`).
   Data symbols need `ExtName` to distinguish data from functions (reloc target name only).
4. **Asm/Encode**: `csel xd, xn, xm, cond` (already printed for `JTSequence`; add standalone
   instruction); **fix `BitOp.rev32` at `size32`**: Cranelift emits opcode `0b000010` with
   `sf = 0` (= `rev wd, wn`, `emit.rs:971`); `FV/Backend/Encode.lean` currently throws
   ("rev32 has no 32-bit form") and `Asm.lean` prints `rev32`; both must produce `rev w`.
   `LoadExtNameGot` for data symbols: same `adrp :got:` / `ldr :got_lo12:` +
   `R_AARCH64_ADR_GOT_PAGE`/`R_AARCH64_LD64_GOT_LO12_NC` as GOT calls (`FV/Backend/Obj.lean`:
   emit the relocations against an undefined data symbol, `STT_NOTYPE`).
5. **Drivers**: `lean-backend` run through `clif-native --functions-obj`: `; data:` objects are
   already assembled and linked by `clif-native`, so no change expected.
6. **Tests**: fixtures `FVTest/Clif/fixtures/e-v2-*.clif` + runtests `select.clif`,
   `smin.clif`/`smax.clif`/`umin.clif`/`umax.clif` (integer parts), `bswap.clif`,
   `bitrev.clif`: Lean backend native == Cranelift native == `Clif.run`; corpus 114/114,
   runtests 2791+ / 0 fail / 0 disagree; `scripts/lean-backend-encode-check.sh` byte-identical;
   `scripts/rust-clif/smoke.sh` without `--drop-nop` (baseline 368/933 with nop dropped).
