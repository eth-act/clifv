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
| 5. Survey to 933/933 (**done**, `agent/rust-i128`) | **933/933 compiled** (debug 454/454, release 239/239, release-oc 240/240). The 41 i128 functions are legalised before the backend by **`Opt.Legalize128`** (`FV/Opt/Legalize128.lean`) — the DECIDED design: no backend/proof change, a CLIF→CLIF pass that rewrites `i128` away the way Cranelift's legalizer does. Every `i128` value becomes an `(lo, hi)` pair of `i64` values: `iadd`/`isub` via the carry/borrow chain, `imul`/`umulhi`/`smulhi` via cross products, `band`/`bor`/`bxor`/`bnot` pairwise, `icmp` lexicographic, `uextend`/`sextend` (`hi = 0` / `sshr lo, 63`), `ireduce` = `lo`, `iconcat`/`isplit`/`bitcast` are the pair, `select`/`bmask`/`bitselect` pairwise, `iabs`/`clz`/`ctz`/`cls`/`popcnt`/`bitrev`/`bswap` from the halves; shifts/rotates by the amount mod 128 with a half-crossing `select` (constant amounts folded); loads/stores as two `i64` accesses at `+0`/`+8`; block params/branch args split; signatures become even/odd `i64` register pairs with an unused `i64` pad reproducing the AAPCS64 skipped register (Cranelift aarch64 `compute_arg_locs`, for returns too), at call sites and in the `fnN`/`sigN` declarations; `udiv`/`sdiv`/`urem`/`srem` at `i128` call `__udivti3`/`__divti3`/`__umodti3`/`__modti3` (freestanding C long division in `rust-runtime.c`; byte-exact `Clif.Rust.env` semantics with the `int_divz`/`int_ovf` traps of the opcodes they replace, so `Clif.run` original and legalised agree). `lean-backend` legalises automatically when a function mentions `i128` (before the mid-end) and flags legalised functions unverified (`i128 legalized (outside backend_correct)`, via `compileFileWith`'s `preUnverified`); the backend's value model and all proof files are untouched. Differential `clif-filetest --legalize128` (every run line through the original and the legalised program): the 31 i128 runtests files 742 pass / 0 fail / **0 disagree** (the 8 `fcvt_*`/float lines are outside `Clif.run` too), survey smoke **0 disagreements**; native (`--functions-obj`, qemu): i128 runtests 735 pass / 0 fail / **0 disagree** vs Cranelift's own aarch64 code, smoke **101/101 pass vs rustc/LLVM** (was 88 pass / 13 not-compiled). `tools.sh`: **933/933** compiled, 0 unsupported. Gates: filetests corpus **114/114**, runtests **4067 pass / 0 fail / 0 disagree** (was 3085); encode-check **1132 identical / 0 differ**; `lean-e2e-check` **910 accepted / 0 rejected** (22 out of scope), formsCoveredB 910 / 0 not covered; `lake build FV.E2E` green. Not legalised (stay unsupported, as `Clif.run` does not run them either): the `fcvt_*`/float i128 runtest functions. Pre-existing (recorded for the integrator): `clif-native`'s prebuilt blame cannot attribute an undefined *data*-symbol reference (`%fn_ptr_table`'s `symbol_value %alloc33`) → "undefined symbols … not referenced by any CLIF function" for `--functions-obj` runs of files with undefined data symbols; independent of i128. |
| 6. `panic=unwind` in `cargo fv` (**done**, `agent/fv-unwind`) | Lean objects carry `.eh_frame` (unverified, `FV/Backend/Unwind.lean`); cg_clif with its `unwinding` feature (`scripts/build-cg-clif-unwind.sh`) supplies landing pads; functions with `try_call` fall back ("landing pad"). See §"Step 6". |
| 7. Dependencies through the Lean backend (**done**, `agent/fv-deps`) | `cargo fv` compiles every crate built for the target (members + registry/git/path dependencies); host crates (build scripts, proc macros and their deps), std (prebuilt) and `--members-only`/skip-deps opt-outs stay as before. examples/deps (42 crates.io dependencies, offline) SAME vs LLVM debug/release and with `--trap-replaced`; per-crate coverage, link-map attribution and an exec trace in §"agent/fv-deps". |

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

## Step 6: `panic=unwind` (`cargo fv`, branch `agent/fv-unwind`)

**Findings.**

- The shipped `rustc-codegen-cranelift-preview` of nightly-2026-09-26 (rustc 5ceaf6608) is
  built without cg_clif's `unwinding` cargo feature (`Cargo.toml`: "Not yet included in
  unstable-features for performance reasons"). With it off, `codegen_fn` skips every MIR
  cleanup block, `codegen_call_with_unwind_action` turns every unwind action into
  `Unreachable` (plain `call`, no `try_call`), the `catch_unwind` intrinsic is a plain
  `call_indirect` returning 0, and the CIE has no personality/LSDA. Checked: with
  `-Cpanic=unwind`, a function with a `Drop` local has no `try_call`; plain `cargo test
  -Zcodegen-backend=cranelift` fails a `catch_unwind` test and a Drop-during-unwinding test
  that LLVM passes, while `#[should_panic]` passes (libtest's catch is LLVM code).
- cg_clif puts each function in its own `.text.subsection` and relocates its FDEs against those
  section symbols, so its FDEs never describe Lean code after the merge (the weakened cg_clif
  copy keeps its FDE and loses it with `--gc-sections`).
- Built from the same commit's sources with `--features unwinding` (rustc-dev component,
  `-L native=<sysroot>/lib` for libLLVM), cg_clif emits `try_call fnN(args), sigN,
  blockK(ret0), [ tag0: blockL(exn0) ]`, cleanup blocks ending in `_Unwind_Resume`, and an
  LSDA per function; `catch_unwind` and Drop-during-unwinding then match LLVM.
  `normalize.py` and `clif-data-export` handle these CGUs unchanged. Under `-Cpanic=abort`
  the same build adds terminate `try_call`s (rustc's `abort_unwinding_calls`: calls into
  unwinding std from a nounwind body), so `--panic-abort` keeps the shipped cg_clif.

**Decisions.**

1. The Lean backend emits `.eh_frame`: CIE as Cranelift's aarch64 `create_cie` with cg_clif's
   `pcrel|sdata4` FDE encoding; per function `PushFrameRegs` (after `stp x29, x30`),
   `DefineNewFrame` (after `mov x29, sp`) and one `SaveReg` row after each callee-save store of
   block 0 (CFA offset = slot − 16 − frameSize); `pc_begin` `R_AARCH64_PREL32` against the
   `.text` section symbol. Unverified, outside `InSubset`/`backend_correct_final`; the proofs
   are untouched (only `FileAsm` gained a defaulted field and `elfObject` an optional
   argument). `unwindRows` rejects (compile error → fallback) a function whose code does not
   start with exactly the prologue and the save stores; none does in the gates. `.text` is
   byte-identical (encode-check 1132/1132).
2. Landing pads: **fallback**, not an unverified `try_call` lowering. A function whose CLIF
   has `try_call`/`try_call_indirect` keeps cg_clif's code (reason "landing pad"), which has
   the landing pads and LSDA. Lowering `try_call` (exception edges and payload registers in
   the VCode, regalloc across exceptional edges, LSDA/`.gcc_except_table` and the personality
   in the CIE) is the next step; it would recover 17–23% of the functions in the examples.
3. `cargo fv` defaults to panic=unwind with the unwinding cg_clif when
   `target/cg_clif-unwind/librustc_codegen_cranelift.so` exists (else the shipped one, with a
   note; then the reference is plain cg_clif, `BASELINE=cg_clif examples/compare.sh`);
   `--panic-abort` restores `-Cpanic=abort -Zpanic-abort-tests` with the shipped cg_clif.

**Evidence.** fv-demo gained six unwinding tests (catch with payload, Drop order during
unwinding, nested catch + `resume_unwind`, `should_panic` through Lean → cg_clif → Lean, and
x19–x28 saved by Lean frames between panic and catch). compare.sh SAME vs LLVM: fv-demo
18/18 debug and release, survey 53/53 debug and release (50 + 3 ignored). With the shipped
cg_clif: fv-demo 14/18 = plain cg_clif's outcomes (SAME with `BASELINE=cg_clif`), survey
53/53 = LLVM. Negative control: with the save rows removed, the fv-demo test binary crashes
(SIGSEGV) during unwinding. Cross-check against Cranelift: for `unwind::churn` (fv-demo,
debug), cg_clif's FDE and the Lean FDE (`llvm-dwarfdump --eh-frame` of the two test
binaries) give the same rules at the calls: CFA = x29+16, x29/x30 at CFA-16/-8, x19…x28 at
CFA-96…-24; only the row positions differ (Cranelift saves with `stp` pairs in the prologue,
the Lean frame with one `stur` per register after `sub sp`). `clif2obj` emits no `.eh_frame`,
so the comparison uses cg_clif's objects.

**Gates.** filetests corpus 114/114 (extrt 22/22), runtests 4067 pass / 0 fail / 0 disagree;
encode-check 1132 identical / 0 differ (`.text` unchanged; the objects only gain `.eh_frame`,
`.rela.eh_frame` and the `.text` section symbol); `lean-e2e-check` 910 accepted / 0 rejected,
formsCoveredB 910 / 0 not covered; `lake build FV.E2E` and `FV.E2E.OptProven` green.

## agent/fv-trycall: `try_call` lowering, landing pads and LSDA

(Superseded in part by agent/trycall-proof: `try_call` of an extern is inside
`E2E.backend_correct_final` for its normal return, reported "verified (normal returns; unwinding
trusted)"; `try_call_indirect` stays unverified. See `docs/contracts/e2e.md`, "`try_call`".)

Implemented (commits on `agent/fv-trycall`): `Clif.Terminator.tryCall`/`tryCallIndirect` with
exception tables (parser/printer in Cranelift 0.136.1 syntax: `sigN, block(ret0), [ tagN: block(exn0),
default: …, context vN ]`); `Clif.run` models only the normal return (call, results bound to
fresh values, `jump normal(retN…)`; no unwinding in `Clif.run`); `termE` excludes them
(unverified: "try_call / landing pads (outside backend_correct)"). Backend: the terminator data
goes through Cranelift's ISLE `lower_branch` try_call rules (`exception_sig`, `try_call_info`,
`gen_try_call_rets` with the x0/x1 payload vregs, a payload in a return register sharing its
vreg); the emitted call becomes the `MInst.tryCall` terminator (regalloc2 `branch` with fixed
defs, SystemV clobbers; every successor is an edge block, so each has one predecessor; the
Lean checker keeps the defs — `isBranch` stays false — and rejects any edit after the call).
Emission `bl/blr; b continuation`; `callSites` + `lsdaBytes` write cg_clif's LSDA
byte-for-byte (checked on `core::intrinsics::disjoint_bitor`: identical call-site table
`[0xb,0xc)→0x14 cleanup, [0x1f,0x20)→0`), a `zLPR` CIE with `DW.ref.rust_eh_personality`
(`lean-backend --personality`, passed by `cargo fv`). `Legalize128` handles i128 try_call
arguments/returns. `cargo fv` no longer falls back on landing pads; `normalize.py` keeps the
`sigN` of try_calls.

Results: `examples/compare.sh` SAME vs LLVM — fv-demo 18/18, survey 53/53, vendor 189/189,
debug and `--release`. fv-demo debug `cargo fv build`: fallbacks 81 → 4 (3 skip + 1 i128, the
latter fixed since: `cargo fv test` units 6 = skip only); the unwinding tests' landing-pad
owners (`unwind::guarded`, `catch_churn`, `rethrow`, `catch_unwind`, `do_catch`, the test
closures) are Lean-compiled. DECISIONS: tail/preserve_all callees and exception-table `context`
items are rejected (compile error → fallback; cg_clif emits neither), so the runtest
`try_call.clif` (tail callee) stays unsupported; tags other than cg_clif's 0/1 have no LSDA.
Proof repairs: `HeadNoCI`/`NoCallIndirect` (Opt simulation) now also exclude try terminators
(conservative: every program of the pre-try_call syntax still satisfies them), `lstep` is stuck
on them. The other repairs are new constructor arms: `termEval`/`lstep` are stuck on try
terminators (vacuous arms in `Unreachable`, `GvnEdit`, `SimpSim`, `SimpLoop`), `ExnTable.mapVals`
congruence/identity/composition lemmas (`mapTerm_*`), `MInst.tryCall` operand arms
(`LowerRename`, `RegLevelDriverSem.visit_mapRegs`), `setTargets` of a `tryCall` (keeps its
operands; `csem` of it ignores the labels: `setTargets_cases` gains that case), and
`LowerSim.Hyps.noTry` (from `Compile.noTry_of_functionE`, like `noTail`).

Gates (final): `lake build FV FVTest FV.E2E FV.E2E.OptProven` green; `#print axioms` of
`E2E.backend_correct_final`/`backend_correct_opt_proven`: propext, Classical.choice, Quot.sound
+ `_native` only; filetests corpus 114/114 (extrt 22/22), runtests 4672 pass / 0 fail / 0
disagree; encode-check 1260 identical / 0 differ; `lean-e2e-check` 910 accepted / 0 rejected /
0 not covered; `compare.sh` SAME: fv-demo 18/18, survey 53/53, vendor 189/189, debug and
`--release`. Fallbacks (`cargo fv test`, panic=unwind): fv-demo 6/6 (skip), survey 0/0,
vendor debug 15 (12 lowerCheck: once_cell `initialize` test closures, `certOk` fails on their
unreachable cleanup blocks — no `try_call`, same lowering as before this branch; 3 TLS),
vendor release 3 (TLS); no landing-pad fallbacks. Negative control: with the LSDA emission
disabled in `Obj.lean`, fv-demo's `catch_unwind_through_lean_frames`,
`drop_runs_during_unwinding`, `nested_catch_and_resume` and `callee_saved_survive_unwinding`
fail (14/18 pass).

## agent/fv-lcheck-tls: the last fallbacks (dead blocks in `lowerCheck`, `tls_value`)

**lowerCheck on dead blocks.** The 12 vendor debug rejections were the test instances of
`once_cell::imp::{impl#4}::initialize::{closure#0}` (4 CLIF shapes). `lean-e2e-check` on the
`--keep-temps` split CLIF: `cert block 11` fails `cclosed`. Block 11 (`block9`) has no
predecessor: cg_clif's cleanup blocks are dead without landing pads, and
`block9 → block14 → block17/block20/… → block13` are reachable only from it. `inFix` starts from
"every value" and intersects over predecessors, so a block without one keeps every value at its
entry, including `v59 = icmp eq v54, v58` (block14) whose operand `v54 = v37` is defined in
block9 itself; `closedOk` (every available value's definition operands available) then fails.
The lowering is right (not a backend bug); the certificate is incomplete only in the untrusted
dataflow. Fix: `inStep` keeps a value at a block entry only if its definition's operands are
available there too (`defArgs`); the rounds still descend. On blocks reachable from the entry
the greatest fixpoint was already closed (every value available on all paths from the entry has
its operands available too), so previously accepted functions keep the same certificate. The
soundness proof (`lowering_of_check`, `cert_of_check`) takes `inFix`'s result as an arbitrary
list, so no proof changed. Repro: `corpus/clif-regress/dead_cleanup.clif` (a dead block whose
successor uses its result; a reachable join with a dead predecessor), rejected by the old
checker, accepted now, in `lean-e2e-check`'s default corpus; runs agree with Cranelift-native.

**TLS.** cg_clif sets `tls_model=elf_gd` for ELF (`lib.rs`); thread locals are
`gvN = symbol [colocated] tls userextnameJ` and `vK = tls_value.i64 gvN`. Cranelift lowers
`tls_value` with `elf_tls_get_addr` → `MInst.ElfTlsGetAddr` (fixed def x0, early def tmp,
no clobbers: the TLSDESC resolver preserves everything but x0/x30), emitted as
`adrp x0 (TLSDESC_ADR_PAGE21) / ldr tmp, [x0] (TLSDESC_LD64_LO12) / add x0, x0, #0
(TLSDESC_ADD_LO12) / blr tmp (TLSDESC_CALL) / mrs tmp, tpidr_el0 / add x0, x0, tmp`. The Lean
backend now does the same: `Clif.GlobalValue.tlsSymbol` + `Clif.Inst.tlsValue` (parser, printer,
`Clif.run` with one thread: the image's symbol), instruction data `UnaryGlobalValue`/`TlsValue`
with its own operand (`Opnd.tlsGlobalValue`, so `symbol_value_data` of `symbol_value` operands is
unchanged), the `tls_model` extractor returns `ElfGd` (cg_clif's flag, as `is_pic`), the
ISLE rules `lower 3217` / `inst 4918` fire (outside the emitter-subset closure, like the
atomics), `MInst.elfTlsGetAddr`, `Insn`s for the four TLSDESC forms and `mrs`, the Arm model
gains `BR.Mrs` (decode + `decode_armBits_Mrs`; `exec_mrs` stops: no system registers), and
the object marks the variables `STT_TLS`. Outside `Compile.functionE`, reported "tls_value
(outside backend_correct)"; the stack-slot allocator rejects it. Checks: Cranelift's
`isa/aarch64/tls-elf-gd.clif` precise output is reproduced register for register
(`corpus/clif-regress/tls_elf_gd.clif`), the objects match `llvm-mc` (encode-check, now also
comparing undefined-symbol types) and cg_clif's code for the vendor accessors, and
`rust-lld` relaxes the sequence to local-exec in the static test executables. fv-demo gained
`tls` + `thread_locals` (const and lazy thread locals, a second thread), which passes under
`cargo fv test` and `--trap-replaced`.

Fallbacks (`cargo fv test --no-run`, panic=unwind): vendor debug 15 → 0 (verified 2533 → 2545,
tls_value 3), vendor release 3 → 0 (tls_value 3), fv-demo 6/6 (skip, tls_value 4), survey 0/0.

Gates: `lake build FV FVTest FV.E2E FV.E2E.OptProven` green; `#print axioms` of
`E2E.backend_correct_final`/`backend_correct_opt_proven`: propext, Classical.choice, Quot.sound
+ `_native` only (`lowering_of_check`: the three standard ones); filetests corpus 114/114
(extrt 22/22), runtests 4672 pass / 0 fail / 0 disagree; encode-check 1265 identical / 0 differ
(34827 words, 1297 relocations; random sweep incl. `tlsdesc`/`mrs_tpidr`, decode ok);
`lean-e2e-check` lowerCheck 911 accepted / 0 rejected / 148 out of scope (+1 accepted:
`dead_cleanup`; +2 out of scope: the TLS regression functions), prepCheck 911/0, formsCoveredB
911 covered / 0 not covered; `compare.sh` SAME: fv-demo 19/19, survey 53/53, vendor 189/189,
debug and `--release`.

<!-- STATUS-MARKER -->

## agent/fv-fallback: baseline `cargo fv` fallback measurements (worktree `../clifv-wt/fv-fallback`)

Goal: reduce `cargo fv` fallbacks to ~0 on real code. Measured before any change
(`cargo fv build`, mode plain; "fb" = fallback):

| workspace | profile | functions | verified | unverified | fb |
| --- | --- | --- | --- | --- | --- |
| examples/fv-demo | debug | 442 | 322 | 118 | 2 (`metadata.fv.skip`) |
| examples/fv-demo | release | 293 | 202 | 84 | 7 (5× missing `allocNNN`, 2 skip) |
| examples/survey | debug | 454 | 394 | 60 | 0 |
| examples/survey | release | 239 | 184 | 42 | 13 (all missing `allocNNN`) |
| examples/vendor (new) | debug | 690 | 515 | 165 | 10 (9 atomics/fence/bmask) |
| examples/vendor (new) | release | 318 | 187 | 115 | 16 (8× missing `allocNNN`, 8 atomics/fence/bmask) |

New `examples/vendor` workspace (commit 83c0e87): vendored dep-free crates.io crates from
`~/.cargo/registry/cache` — crc32fast 1.5.2, itoa 1.0.18, memchr 2.8.3, hex 0.4.3, bitflags
2.13.2, cfg-if 1.0.1, once_cell 1.21.4 (+ `harness` crate with reference-value tests).
Vendoring patches: dev-dependencies pruned ([[bench]]/[[test]]/[[example]] sections removed,
tests/ and benches/ deleted); `quickcheck!` blocks in crc32fast/memchr replaced by
deterministic LCG-driven `#[test]`s; `pretty_assertions::assert_eq` imports in hex dropped;
itoa's optional `no-panic` dependency removed. Purpose: real-world code to measure and drive
out the remaining fallback reasons.

Fallback reasons collected (top, vendor debug+release combined):
1. `unsupported: atomic_load/atomic_store/atomic_rmw (xchg, sub)/atomic_cas/fence ... is not in E` — once_cell's `race` module (AtomicUsize/AtomicPtr/AtomicBool).
2. `unsupported: bmask.i8 ... is not in E` — harness/bitflags code.
3. `references allocNNN, which cg_clif's object does not contain` — release-only: the Lean backend compiles the unoptimised CLIF, which still contains (dead) panic paths whose `Location` data objects cg_clif's optimiser removed from its object; fix options: retry with the `.opt.clif` dump (preferred), or emit a private copy of the missing read-only data.
4. `cfg-if (lib): codegen unit fell back entirely: CLIF dumps … missing` — cfg-if defines no functions, cg_clif writes no dump dir; cargo-fv reports a unit-level error (noise, no code lost).

### agent/fv-fallback: implemented (final)

All four steps landed (commit series on `agent/fv-fallback`):

1. **Release missing-`allocNNN`** — `cargo fv` (`pipeline.rs`) runs `clif-data-export` and
   `normalize.py` for both stages (gvmap entries are stage-filtered in normalize.py) and, when
   the unopt compile's object references an `alloc*`/`data_*`/`u0_*` name absent from cg_clif's
   object ("removed by Cranelift's optimiser, or unmapped"), retries with the normalised
   `.opt.clif` dump (separate output object; a failing retry keeps the unopt result and its
   reference check reports the original reason). The optimised dump matches the code cg_clif
   actually emitted, so it references only data that exists (verified on
   `core::intrinsics::rotate_left`: the release unopt dump references `alloc294` only through
   its dead panic block, gone from cg_clif's object). DECISION: private data copies rejected —
   the bytes are not recoverable from cg_clif's object at all. Macro-only CGUs (cfg-if): cg_clif
   writes no dump dir; `cargo fv` now reports each text symbol as a fallback row instead of a
   unit-level error.
2. **bmask + 3. atomics** — lowered by the full exported ISLE program (not the emitter
   closure): the non-LSE rules `load_acquire`/`store_release`, `atomic_rmw_loop`/
   `atomic_cas_loop`, `lower_bmask` (`use_lse` fails → cg_clif's `has_lse=0` path).
   DECISION: the opcodes are NOT added to `isle2lean`'s `E_OPCODES` (an intermediate commit did,
   regenerating `Closure.lean` to 486 rules; reverted): closure roots must lie in the proven
   families, and the excluded-root refutations need the atomic opcodes outside `eOps`. The
   proofs instead learn that an E instruction (`Compile.instE`) never has an atomic opcode name
   (`IselExclData.instE_atomic_ne`; `instNames`/`eNamePairs` gained the new arms).
   `instData` arms build the
   `InstructionData` (`LoadNoOffset`/`StoreNoOffset`/`AtomicRmw`/`AtomicCas`/`NullAry`/`Unary(Bmask)`);
   new MInst: `loadAcquire`/`storeRelease` (ldar/stlr), `atomicRmwLoop`/`atomicCasLoop` (emit-time
   LL/SC loop expansion transcribed from Cranelift's `inst/emit.rs`: ldaxr/extend/op/stlxr/cbnz
   over fixed x24–x28, with emit-time labels `Lbl.loop`), `csetm` (csinv), `fence` (dmb ish).
   regalloc operands: `Constraint.fixed` as `aarch64_get_operands` (x25/x26 in, x27/x24/x28
   out) with one conservative deviation: the x28 def is registered for `xchg` too (Cranelift
   omits it; x28 is dead across the instruction either way), which keeps `visitOperands`
   uniform in the op for the rename-commutation proof (`LowerRename.Sim.visit`). The
   stack-slot allocator rejects the loop pseudo-insts. Arm model: new
   decode classes `LDST.Reg_exclusive` (LDXR/LDAXR/STXR/STLXR/LDAR/STLR) and `BR.Barrier` (dmb;
   in the BR group because the DPR `decode_class` proofs require every fixed-bit dispatch to be
   decidable without the opaque sf/op/S bits) with exec (exclusive store writes the success flag
   0 to Rs) and `decode_armBits_*` theorems; `arm-cosim.sh` co-simulates `dmb ish`, `ldar`,
   `stlr`, `ldaxr` against qemu (a lone `stlxr` cannot be: qemu fails it without a monitor,
   the model's exclusive store always succeeds). Encoders checked against llvm-mc
   (`lean-backend-encode-check.sh`, the compiled runtests plus random-sweep forms `csetm`,
   `ldar_stlr_ldaxr`, `stlxr`, `dmb` with the decode check). Differential execution:
   the atomic/bmask/fence runtests agree with Cranelift-native (621/621 after fixing the i32/i64
   min-max comparison width and the i64 smin/smax operand extend — both transcriptions now match
   `emit.rs` exactly). `FVTest/E2E/Check.lean` skips functions outside `Compile.functionE` (they
   are outside the theorem); `Backend.unverifiedReason?` reports "bmask / atomic instructions /
   fence (outside backend_correct)". `E2E.InSubset`/the theorems are untouched.
4. **TLS** — never showed up as a fallback (no vendored crate or example uses `#[thread_local]`;
   the survey dumps declare `set tls_model=elf_gd` but contain no `tls_value`), so no code
   change; the parser still rejects TLS globals (`FV/Clif/Parse.lean:383`).

Before/after (`cargo fv build` + `cargo fv report`; "before" was measured with panic=abort,
before fv-unwind was merged, so the comparable "after" is `--panic-abort`; under the default
panic=unwind the landing-pad fallbacks of the fv-unwind design come on top):

| workspace | profile | fb before (abort) | fb after (abort) | fb after (unwind) | of which landing pad | of which skip |
|---|---|---|---|---|---|---|
| fv-demo | debug | 2 | 3 | 81 | 78 | 3 (`metadata.fv.skip`; 2 before) |
| fv-demo | release | 7 | 3 | 77 | 74 | 3 |
| survey | debug | 0 | 0 | 55 | 55 | — |
| survey | release | 13 | 0 | 47 | 47 | — |
| vendor | debug | 10 | 0 | 41 | 41 | — |
| vendor | release | 16 | 0 | 31 | 31 | — |

Remaining fallback reasons: `package.metadata.fv.skip` (fv-demo, deliberate) and, with
panic=unwind, landing pads (try_call; the Lean backend emits no exception tables). The
atomic/bmask/fence functions (vendor: 9 debug, 7–8 release) report "bmask / atomic
instructions / fence (outside backend_correct)": `cargo fv` prefers lean-backend's own
unverified reason over its "rule fired outside the emitter-subset closure" warning, which
the (non-closure) atomic rules trigger by design.

Gates: `lake build FV FV.E2E FV.E2E.OptProven FVTest` green, `#print axioms` of
`E2E.backend_correct_final`/`backend_correct_opt_proven`: standard + `_native` only;
`lean-backend-filetests.sh` corpus 114/114 (+ extrt 22/22), runtests 395 files: 4672 lean
passes, 0 fail, 0 disagree vs Cranelift-native (atomic/bmask/fence files: 621 passes, the
big-endian and 128-bit atomic files are not compiled by Cranelift-native either);
`lean-backend-encode-check.sh` 1260 functions identical, 0 differ (34368 words, 1085
relocations); `arm-cosim.sh` 169 forms / 33800 vectors, 0 failures; `lean-e2e-check` lowerCheck
910 accepted / 0 rejected / 146 out of scope (22 before; +124: the atomic/bmask/fence runtest
functions now lower but are outside `Compile.functionE`), prepCheck 910/0, formsCoveredB 910
covered / 0 not covered; `examples/compare.sh` fv-demo 18/18, survey 53/53, vendor 189/189
(debug + release, SAME).

## Native coverage (branch `agent/native-cov`)

Every one of the 933 survey functions runs natively, Lean-backend code against Cranelift's
own aarch64 code for the same CLIF, on generated inputs, with all observable outputs
compared. Command: `scripts/rust-clif/diff-native.sh` (driver `clif-native --diff`,
`rust/crates/clif-native/src/diff.rs` + `diffharness.c`); negative control
`scripts/rust-clif/diff-native-selftest.sh`.

### How a function is exercised

- **Per crate/profile** the unopt dump is normalised with its recovered data image and
  callee names (`clif-data-export --fnmap`, `normalize.py --fnmap`), compiled once by `lean-backend` (all functions) and once by
  Cranelift (inside the driver). Both executables link the *same* freestanding harness,
  Cranelift-compiled trampolines (`load args → call → store results`, so the ABI boundary is
  identical), the `; data:` objects, `rust-runtime.c` (`mem*`, `__*ti3`) and generated stubs;
  only the object with the file's functions differs. Calls between corpus functions go to the
  engine's own code (the whole crate is linked).
- **Externs**: the Rust allocator entry points (`__rust_alloc` & co., mangled or not; `--alias
  SYM=TARGET` for others) go to a deterministic bump heap in the harness; `__rust_u128_mulo` is implemented in the harness; every other extern
  (the `core` panic entry points, `fmt`) is a stub that traps — the outcome `extern <symbol>`
  (exact for the never-returning panics); symbols referenced only as data that cg_clif's
  optimiser dropped (dead `allocN` references) are unmapped absolute addresses.
- **Inputs** (PRNG per (seed, function, vector), identical in both executables): a 64 KiB
  arena at a fixed address filled with pointers into itself, small integers, zeros, random
  words, pointers to data objects (vtables preferred) and to fixed-address per-function
  thunks. Parameter kinds come from a CLIF dataflow analysis (`param_kinds`): *pointer* (flows
  through `iadd`/`isub`/`select`/block args/stack slots/calls into a load/store address, a
  `mem*` pointer, or `self` of an indirect call) → mostly arena pointers; *sret* → a reserved
  arena tail; *code pointer* (reaches a `call_indirect` callee) → a thunk of a function with
  the called signature; *vtable* (the address a callee is loaded from) → a data object that
  points at functions; integers → a mix of small values, boundaries (0, ±1, `MIN`/`MAX` per
  width, 2^32, …), random words.
- **Compared per call**: the outcome class (returned / `trap <code>` via each engine's trap
  table / `extern <symbol>` / signal + faulting symbol + fault address), return values, and
  every memory word the call can write (arena incl. everything reachable through the pointer
  arguments, the heap, the writable data objects) as an exact word-level diff. Code addresses
  are canonicalised (a word equal to a function address becomes a token; data objects and
  arena words point at fixed-address thunks instead of the functions, so their bytes are
  engine-independent), stack addresses become one token (frame layouts differ).
- **Nondeterminism**: each vector runs under two configurations per engine — different stack
  base, and complementary fill patterns for the fresh stack and heap. A bit that differs
  between one engine's two runs depends on uninitialised bytes (unspecified in CLIF: e.g.
  `Option<u32>` padding copied out of a stack slot) and is not compared (`agree_masked`
  counts the vectors where that happened); everything else must match exactly. Timeouts
  (500 ms virtual CPU per call), stack overflows and harness crashes are skipped and counted.
  A function with fewer than 50 compared vectors gets more (rounds of 64, up to 512).

### Results (seed 24301, 64 vectors per round)

| profile | functions | vectors | agree | of which masked | disagree | skipped |
| --- | --- | --- | --- | --- | --- | --- |
| debug | 454 | 29 568 | 29 040 | 1 213 | **0** | 527 timeout, 1 nondet. memory |
| release | 239 | 15 744 | 15 300 | 608 | **0** | 444 timeout |
| release-oc | 240 | 15 744 | 15 338 | 599 | **0** | 406 timeout |
| **total** | **933** | 61 056 | **59 678** | 2 420 | **0** | 1 378 |

A second seed (`SEED=7`) gives the same picture: 933 functions, 59 664 agreeing vectors
(2 359 masked), **0 disagreements**, 0 functions below the minimum.

Every function has ≥ 50 compared vectors (minimum 50: `sum_range`, `rev_step`,
`nested_loops`, whose large random bounds time out; 0 functions below the minimum). Per crate
the table is in `DIFF_WORK/summary.md` (27 crate/profile rows, all 0 disagreements); 412 of
the 933 are inside `E2E.backend_correct_final`, the other 521 are compiled-but-unverified
(calls, sret, i128 legalised, indirect calls) — the differential covers both.

Agreed outcomes: 42 072 returned, 9 052 SIGSEGV (wild pointers, both engines at the same
fault address), 5 982 `extern` (panics / fmt stubs), 2 572 `trap user1`. 895 of the 933
functions return normally on at least one vector; the other 38 are functions whose every
generated input panics or faults: 19 always reach an extern (`fmt`-based `Debug` impls, error
paths such as `unwrap_failed`), 8 always hit `trap user1` (e.g. `opt_u64_zip`), 11 always
fault (dyn-dispatch helpers whose `self`/vtable layout random memory rarely satisfies).
Externs: 163 trap stubs, 15 allocator aliases, 32 dead data references over the 27 files.

Negative control (`diff-native-selftest.sh`, one-instruction mutations compiled by the Lean
backend and diffed against Cranelift on the original): `add_u32` `iadd`→`isub` (return
value) 30/32 vectors disagree; `make_array` store offset 63→62 (memory through `sret`) 32/32;
`swap_ends` index 1→2 (memory through pointer args / panic path) 19/32; unmutated controls in
the same files 0 disagreements.

### Bugs found

- **Lean backend, `sret` ABI** (fixed on main in `f52e514`, found independently by
  `cargo fv`): `sigArgLocs` let the sret parameter consume `x0`, shifting every later
  parameter by one register at entries and call sites (Cranelift: sret in x8, the others
  from x0). Before the fix: 3 151 disagreeing vectors — 3 134 in sret functions and their
  callers (e.g. `vec_squares(i64 sret, i32)` read its bound from x1), the other 17 the
  code-address artefact below; bisected with `clif-native --diff --lean-only SYMBOL` (Lean
  code for the named functions only, Cranelift for the rest).
- **Harness artefacts removed on the way** (not compiler bugs): partial reads of code
  addresses stored in memory (→ thunks with engine-independent bytes), random-vs-random
  masking of uninitialised bits (→ complementary patterns).
- **clif-native (step 1 follow-up)**: `--functions-obj` runs bailed on undefined data
  symbols (`%fn_ptr_table`'s `symbol_value %alloc33`); the blame now covers `symbol_value`
  references (also through `; data:` items) in both modes. `smoke.sh` builds `smoke.clif`
  with the recovered data image (+ every function/data object it points at) and runs
  `Clif.run` with `--rust-env`: **103/103 run lines pass natively and under `Clif.run`**
  (was 101/103).

### Limits

- Inputs are random, not coverage-guided: deep invariants (a valid `&dyn Trait` behind two
  pointers, a well-formed `Vec` of `Vec`s) are hit only occasionally; see the 38 functions
  above. Loops over random bounds time out (skipped, counted).
- Masked bits: a miscompilation that only changes bits derived from uninitialised memory is
  invisible (CLIF leaves those bits unspecified anyway).
- The comparison is Lean backend vs Cranelift on the same (normalised) CLIF, not vs cg_clif's
  own object (whose code for the same functions is Cranelift output too, so this is the same
  oracle without cg_clif's data/symbol layout); calls into `core`/`alloc` beyond the
  allocator are stubs.

## agent/fv-deps: dependencies compiled by the Lean backend

**Change.** `fv-rustc` used to compile only workspace members (`Config::is_member`); now any
rustc invocation that codegens for `--target aarch64-unknown-linux-musl` (emit `link`, crate
type lib/rlib/bin or a test harness) goes through the pipeline, unless `--members-only`
(own target dir `target/fv/<mode>-members`) or the package is in `skip-deps`
(`[package|workspace.metadata.fv]`, `FV_SKIP_DEPS`). Host crates are recognised from rustc's
arguments, not guessed: cargo compiles build scripts (`build_script_build`), proc macros
(`--crate-type proc-macro`) and their dependencies without `--target`. Dependency invocations
differ from members only in flags the pipeline does not look at (`--cap-lints`,
`-C embed-bitcode=no`, `-C metadata`); the unit is `<crate><extra-filename>` like the rlib, and
hashed mangling makes their symbols unique. Nothing in `pipeline.rs` had to change for them.

* **Stamp**: a change of the Lean tools/settings now deletes the profile's whole target-side
  directory (`target/fv/<mode>/aarch64-unknown-linux-musl/<profile>`: members, dependencies
  and their build-script runs) and the unit reports, instead of `cargo clean -p` per member.
* **Throttle**: `FV_JOBS` was per codegen unit; with ~40 crates compiling at once that is
  unbounded, so `lean-backend` runs now take one of `FV_JOBS` file-lock slots
  (`tmp/slots/<k>.lock`, `File::try_lock`) shared by the whole build.
* **Report**: `UnitReport.dep`; `Report.members`/`deps` next to `totals`; dependency rows have
  kind `dep`; reasons by count per group. Each linked executable gets `binary.origin` from an
  lld link map (`-Map`, written by linker mode): every function symbol (distinct address) is
  attributed to its input object — Lean (marker) or cg_clif code of a unit we compiled (rlib
  `lib<unit>.rlib` with a unit report, or the executable's own `<unit>.*.rcgu.o`), the sysroot
  (`prebuilt`: std, core, alloc, compiler_builtins, musl) or anything else (`other`). A first
  attempt attributed by symbol name and misclassified std's local copies of `#[inline]` core
  functions (same v0 name as our units' copies) as ours; the link map is exact.
* **Environment bug found**: build scripts that run `$RUSTC --version` (libc panics; crc32fast
  silently drops its `stable_arm_crc32_intrinsics` cfg) failed under `cargo fv` started from
  this repository: the 1.96 rustup proxy's `LD_LIBRARY_PATH` plus cargo's
  `rustlib/<host>/lib` (which holds a `librustc_driver` with rustc-dev installed) made the
  nightly rustc miss its libLLVM. `cargo fv` now prepends the pinned toolchain's `lib/`. This
  was the unexplained "crc32fast cfg not set by cg_clif" of agent/fv-fallback.

**Results** (examples/deps; details and the per-package table in docs/USAGE.md,
"Dependencies"): debug 21021 functions, 20821 verified, 3 unverified, 197 fallback (your
crate(s) 4056/4028/0/28, dependencies 16965/16793/3/169); release 14587/14461/2/124
(3713/3676/0/37, 10874/10785/2/87). Remaining reasons: floats (f64/f32 types, `f64const`),
NEON SIMD (`i64x2`/`i32x4`: sha2's SHA intrinsics, zmij), 2 release functions of
regex-automata with `i128` values and atomics (`Opt.Legalize128`: "atomics are not
legalised", so the backend reports the raw `iconcat`), and the validation budget for fully
unrolled hash rounds (sha2 `soft::unroll::compress_block`, tiny-keccak `keccakf` in debug).
compare.sh SAME: fv-demo 19/19, survey 53/53, vendor 189/189, deps 16/16, debug and release;
deps also with `--trap-replaced`. Evidence that dependency code is Lean code at run time:
`scripts/fv-exec-trace.py` (qemu `-d exec,nochain` + link map) on the `--trap-replaced` debug
harness: 2421 Lean-compiled regex-automata functions executed, 1578 regex-syntax, 870
aho-corasick, 420 serde_json, 268 num-bigint, 141 regex, 103 rand, 73 sha2, 59 tiny-keccak,
0 executed std functions are Lean (std is prebuilt).

**Not done / open.** std is still the prebuilt LLVM build (`-Zbuild-std` with cg_clif would
put it through the same path). Legalising atomics in `i128` functions and lifting the
validation budget for unrolled hash rounds need FV work (validator + proofs); floats and SIMD
are outside the backend.

