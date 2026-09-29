# Rust route: real Rust crates through the all-Lean CLIF → AArch64 compiler

Work log for the Rust route (`docs/research/rust-clif-survey.md` §"Post-v2" and
`docs/DEFERRED.md` "Rust route extras"). Worktree `../clifv-wt/rust-route`, branch
`agent/rust-route`. Survey corpus: 933 functions (9 crates × debug / release /
release-oc), dumped by `scripts/rust-clif/dump.sh` into `/tmp/rust-clif-survey/out`.

## Status

| Step | State |
| --- | --- |
| 1. Data objects from cg_clif | **done** — `rust/crates/clif-data-export` recovers every data object of the corpus (294/294 data-using functions, 938 objects, 43 560 bytes, transitively closed; 0 mismatches over 933 functions × 3 profiles). Directives + gv table emitted; wired into `normalize.py --gvmap --data-file` and `tools.sh`; smoke runs of constant-table/vtable readers pass under `Clif.run` and the Lean backend natively, agreeing with rustc/LLVM. |
| 2. Panic and mem* externs | **done (Lean side)** — `Clif.Rust.env` (byte-level `memcpy`/`memmove`/`memset`/`memcmp`, panics end the run as `trapped user1`); `clif-filetest --rust-env`; native: `scripts/rust-clif/rust-runtime.{c,s}` (`udf #251`), linked with `clif-native --link` via `lean-backend-filetests.sh`'s `RUST_RUNTIME`. Fixture `scripts/rust-clif/fixtures/mem-panics.clif`: `Clif.run` 4/4, Lean backend + Cranelift-native both 3/3 (the panic command aborts with SIGILL on both, reported as an error on both sides — the documented "aborted" agreement). Documented in e2e.md's trusted list. |
| 3. `sret` | **done (unverified by design)** — `sigArgLocs` places the hidden pointer in x8 (`compute_arg_locs`), `sigRets` legalizes the return (`ensure_struct_return_ptr_is_returned`: x0 = the sret param, also for *call sites*), `isArgReg` admits x8, sret sigs are compiled and flagged unverified (`unverifiedReason?` = "sret parameter (outside backend_correct)"), `InSubset.noSpecial` keeps them outside the theorem (e2e-check: 910 in scope / 22 out). Demo `sret.clif` (corpus `big_make`/`make_shape` + drivers passing a data object as the sret pointer): `Clif.run` 2/2, Lean backend native 2/2 = Cranelift-native = rustc/LLVM byte-for-byte. |
| 4. `dyn`/fn pointers (`call_indirect`, `func_addr`) | **done (native runs verified, flagged unverified)** — `Clif.run` supports both (`stepCallIndirect`, `func_addr` via `mem.symbols`); parser/printer handle `sigN`; the Lean backend lowers both via the exported ISLE rules (`rule_lower_2529`, `func_addr` → `load_ext_name`, `gen_call_ind_info`, `value_slice_unwrap`, `InstructionData.CallIndirect/FuncAddr` term data). Step 4 closes with three commits: (1) both opcodes admitted to the emitter-subset closure (`E_OPCODES` + regenerated `Closure.lean`, 444 rules / 131 roots; `closureRootIds` gains the FuncAddr/CallIndirect root rules 1026/1033) with `instE` admitting them (flagged unverified: `InSubset.noCI`, `unverifiedReason?` "indirect call / func_addr (outside backend_correct)"); (2) **`Clif.Mem.Image.memWith`** — data-object relocations resolve function/extern symbols (stubs registered before `writeItems`; `Program.initMem` routes through it) — without it `Clif.run` of vtable-bearing files was `stuck`; (3) fixture `scripts/rust-clif/fixtures/dyn-vtable.clif`: self-contained `dyn_pick`/`dyn_hash` runs over the recovered Fnv/Xor vtables — 3 `; run:` lines pass in `Clif.run` (3-element FNV hash 2121893058 and XOR 33 agree with rustc/LLVM; addresses are the interpreter's link-time layout — native `%name` run args are future work). DriverHyp/noCI etc. as before; OptProven's `step_eq_lift` callIndirect case owned by the OptProvenFix agent (WIP diff in `/tmp/rustroute3_semsim.patch`).| 5. Re-count | **in progress (this run)** — recount with `scripts/rust-clif/tools.sh`: **863/933 compile** with `lean-backend` (debug 423/454, release 220/239, release-oc 220/240; clif2obj 933/933). Causes by count: `i128 parameter` 31, `prepCheck` 24, `extend to i128` 6, `calls %X, which is not compiled` 5 (transitive), `i128 return value` 4 — i.e. **i128/u128 ≈ 41** and **prepCheck ≈ 24**. `call_indirect`/`func_addr` functions all compile now (the closure work). prepCheck root cause found (OptProvenFix's area): `prepare` drops unreachable vc blocks; `prepCheck.keptOk` walks every vc block and fails on the dropped ones (repro: `/tmp/rust-clif-survey/tools/debug-a_arith.unopt.reader.clif` `%cmp_bool`, vc block 5 unreachable-and-aliased, insts.size 2 vs 1) — `prepCheck` must skip vc blocks absent from vcp. i128 backend scope (unstarted): `sigArgs`/`sigL` must pass an i128 as **two x-registers** (Cranelift's aarch64 ABI; the `add_u128` vcode shows `adds x8, x0, x2` / `adc x1, x13, x3` + the overflow check via `subs`/`sbcs` + `__multi3`-style helper `blr` for `imul`), `buildCtx` must give i128 values `.int 128` types (the ISLE rules match `$I128`), and the exclusion checker's `eCTys`/`AV.tys` must cover it; new MInst encode/sem forms for `adds`/`adc`/`sbcs` (+ proofs = flagged unverified). Clif.run needs nothing: a census confirms every i128 opcode the corpus uses (iadd/isub/imul/band/bor/bxor/ishl/ushr/sshr/icmp/uextend/sextend/ireduce/load/store/udiv/sdiv/urem/srem) already runs.

| 5. Survey to 933/933 (in progress) | **892/933 compiled** (post-merge re-count: debug 437/454, release 227/239, release-oc 228/240), remaining cause: i128 only — 31 `i128 parameter` + 6 `extend to i128` + 4 `i128 return value` (the M7 ABI/`instData` reject i128; the backend's value model is one vreg per value, while Cranelift's i128 lowering needs a two-register `ValueRegs` pair — `lowerFunction` throws "multi-register result"). `Clif.run` **runs the i128 functions correctly** (the corpus's `iadd.i128`/`load.i128`/`iconcat`/… execute; `iconst.i128` is rejected by both readers, as in CLIF — constants come via `iconcat`). `smoke.sh` extended with the `g_u128` corpus functions: **103 run lines, Clif.run 101 pass / 0 fail / 2 unsupported (pre-existing missing panic extern), Cranelift-native agrees 101, Lean backend 88 pass / 13 not-compiled (the u128 functions, pending backend i128)**; expected values from rustc/LLVM. The i128 ABI/lowering is the one remaining compiler feature, to be added flagged
  unverified. Implementation plan (each item touches the lowering simulation, so proof
  repairs are expected — M7 is the only layer involved; the mid-end never sees i128):

  1. ABI (`FV/Backend/Isel.lean`): `sigArgs` admits i128 as 16 bytes; `sigArgLocs` places
     it in an even-aligned register pair (AAPCS64 `next_pair`: x0/x1, x2/x3, …, skipping
     the odd half of a used pair); `sigRets` returns two registers for an i128 return;
     `gen_call_args`/`gen_call_rets`/`gen_call_output`/`gen_return` accept pairs.
  2. Value model (`buildCtx`): an i128 value gets two vregs (Cranelift `ValueRegs` pair;
     today `buildCtx` throws "block parameter v{v} is i128" / "value v{r} is i128" and
     `valReg` is 1:1). Every `.value n` resolution (`put_in_reg` for an i128-typed value)
     must yield the pair; `ctx` needs `valTy` → ValueRegs-width.
  3. `lowerFunction`'s result binding accepts the two-register `regsVec` rows (today it
     throws "multi-register result") and `gen_arg_setup` copies 16-byte stack arguments
     as two 8-byte loads.
  4. `instData`/`instE`: drop the i128 rejections (the opcode → `InstructionData`
     construction is type-generic already); remove `"i128"` from
     `isle2lean/src/closure.rs` `DEFAULT_EXCLUDES` and re-export so the i128-tagged rules
     (51 in aarch64/lower.isle) are not flagged default-excluded; regenerate
     `FV/Isle/Generated/Closure.lean` if the selection changes.
  5. New ISLE externs in `externCtor`: `with_flags` (pairs a `ProducesFlags` producer
     with a `ConsumesFlags` consumer through the flag register: `opportunistic_def` of
     xzr exists; needs the `ProducesFlags`/`ConsumesFlags` model values and the
     `emit_two`-style sequencing), `output_pair`, `value_is_unused`, `add_with_flags_paired`/
     `sub_with_flags_paired`/`mulhi_with_flags_paired`-style helpers, `put_in_reg_zext64`,
     `put_in_reg_sext64`, and the `ConsumesFlagsTwiceReturnsValueRegs`/`FourTimes` result
     plumbing. `MInst` already has `Adc`/`AdcS`/`MAdd` ALU ops — the encoders they need
     exist for the `sret`/`select` work.
  6. Runs: `Clif.run` is already i128-complete (verified against rustc/LLVM via smoke). |

## Step 1: data objects from cg_clif (`clif-data-export`)

### What cg_clif hides where

- cg_clif defines every static data object (panic `Location`s and messages, constant
  tables, constant enum values, vtables) as an **anonymous** data object; cranelift-module
  names its symbol `.Ldata{DataId:x}` (hex; `module.rs:411`). The CLIF dumps only declare
  `gvN = symbol colocated userextnameJ ; COMMENT`, where the comment (`alloc16`, `vtable`)
  names the *allocation*, not the symbol. Nothing in the dumps links the two.
- The link is in each function's code: every `symbol_value` lowers to a
  `load_ext_name_got` instruction (two instructions: `adrp`+`ldr` through the GOT,
  `is_pic=1`) and hence to exactly one GOT relocation pair,
  `R_AARCH64_ADR_GOT_PAGE` (**311**) + `R_AARCH64_LD64_GOT_LO12_NC` (**312** — not 313),
  same symbol, in code order.
- The **`.vcode` file names each load's external name explicitly**:
  `load_ext_name_got xN, User(userextnameJ)` (or `LibCall(Memcpy)`). So zipping the
  `.vcode`'s load lines with the GOT pairs, in code order, gives the ext ↔ symbol mapping
  exactly, with **no order assumption between the CLIF and the code** (cg_clif reorders
  loads at `-O`; CLIF layout order ≠ code order, e.g. `d_loops_iters`
  `_RNx…H4eMvNmZvQEZ`: 10 `symbol_value`s map to pairs in a different order).

### Semantics discovered along the way (verified on the survey objects)

- `userextnameN` is a **per-function** `UserExternalNameRef` over *both* namespaces
  (cranelift-module uses namespace 0 for functions = FuncId, namespace 1 for data =
  DataId; `declare_data_in_func`/`declare_func_in_func` in `module.rs`). A gv and a fn
  declaration can share a ref number; the pair's target kind (Data/Text) disambiguates.
- **One allocation per referencing function**: cg_clif's `anon_allocs` map lives in the
  per-function `ConstantCx`, so the same `alloc5` comment resolves to a *different*
  `.LdataN` symbol (with identical bytes) in each function that references it
  (`d_loops_iters`: alloc5 → `.Ldata6`, `.Ldatae`, `.Ldata12` in three functions). The
  alloc comment is therefore not an identity; data objects are named by their symbol
  (`<crate>_Ldata<N>`) and the gv table maps (dump file, gv) → that name.
- The GOT load of a non-colocated **callee** (`memcpy`, panic functions) is also a
  `load_ext_name_got` in the `.vcode` (its pair targets a function symbol); Cranelift
  *LibCall* loads (`%Memcpy`) likewise. Only pairs whose target is a Data symbol are
  recorded.
- Data→data references inside `.data.rel.ro` may go through the **section symbol**
  (S = section base, A = the referenced offset); the tool resolves them to the covering
  data object.
- Undefined (imported) function symbols (`core`'s panic fns) appear as GOT targets; they
  are skipped, and imported data objects are reported and skipped (none in the corpus).

### Results over the survey corpus (933 functions, all 3 profiles)

| | fns | with data | data objects | data bytes |
| --- | --- | --- | --- | --- |
| debug | 454 | 152 | 480 | 26 224 |
| release | 239 | 56 | 178 | 6 635 |
| release-oc | 240 | 86 | 280 | 10 701 |
| **total** | **933** | **294** | **938** | **43 560** |

(The objects include the transitively-reachable ones — a panic `Location`'s message
string, the 20 `&K[i]` chunks of `sha256_compress` at `-O`, etc.; the earlier count
721/23 049 missed data-reachable-only objects.)

Per-function results are the union of all 27 crate×profile runs; the tool exits non-zero
on any mismatch, and there are none.

(The per-crate numbers are reproducible with `scripts/rust-clif/data-export.sh`; the tool
exits non-zero on any mismatch, and there are none: every `symbol_value` target of the
corpus is recovered, including the 4 debug vtables and the writable `i_alloc` objects.)

Outputs per crate×profile: `<crate>.data.clif` (`; data:` directives, bytes as hex,
pointers as `%sym±addend`) and `<crate>.gvmap.tsv` (`dump-file \t gvN \t %name`).

### Regression gates after the merge of `agent/optproven-fix` (post-step-5 sigN fixes)

`lake build FV.E2E FV.E2E.OptProven`: green (the proof files need `FV_MEMCAP=32G`; 12G
gets the scope OOM-killed mid-`RegallocInsts*`). `#print axioms E2E.backend_correct_final`
and `E2E.backend_correct_opt_proven`: only propext, Classical.choice, Quot.sound plus
`_native` bv_decide certificates (2203 axiom names, all of the allowed kinds).
`scripts/lean-backend-filetests.sh`: corpus **114/114**, extrt **22/22**, runtests **3085
pass / 0 fail / 0 disagree**. `scripts/lean-backend-encode-check.sh`: **971 identical,
0 differ**. `lean-e2e-check`: **lowerCheck 910 accepted / 0 rejected** (22 out of scope),
**prepCheck 910 accepted / 0 rejected**, **formsCoveredB 910 covered / 0 not covered**.
`scripts/opt-difftest.sh`: **0 fail / 0 differ**, survey set **30 checked / 0 rejected**
(after two printer/parser fixes: `Print.Function` emits explicit `sigN` declarations
before the `fnN` decls — a `fn` decl with an inline signature implicitly imports a
signature at the next free index, so a later explicit decl collided as "duplicate entity:
sigN" in the pinned reader; `Parse` keeps only the first declaration of each `sigN` —
cg_clif re-declares the same `sigN` per call_indirect site).

Found (pre-existing on main, recorded): the survey's *stored* `smoke.clif` now has 10 of
its 88 run lines unsupported — `%apply` (4) and `%cmp_bool` (6) are rejected by M7's
`prepCheck` — while the dynamic gate above stays green. The smoke selection is
regenerated by `smoke.sh`, so only the checked-in expectation is stale; flagged for the
integrator.

### Remaining step-1 work (tracked)

- [ ] (done in step (b)) wire into `normalize.py`/`tools.sh`/`smoke.sh` and prove the
      bytes end to end.
- `align=` is not emitted (the `Clif.Image` aligns every object to ≥16 and the
  intra-object offsets are preserved, so placement is value-correct); `tls` and
  imported statics are out of scope (none in the corpus).

<!-- STATUS-MARKER -->
