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

Implementation plan (all flagged unverified via `unverifiedReason?`, theorems untouched):
atomics → add `atomic_load/atomic_store/atomic_rmw/atomic_cas/fence` + `bmask` to
`isle2lean`'s `E_OPCODES`, regenerate `Closure.lean`; `instData` arms (InstructionData
`LoadNoOffset/StoreNoOffset/AtomicRmw/AtomicCas/NullAry/Unary(Bmask)`); MInst variants
`LoadAcquire/StoreRelease` (ldar/stlr), `AtomicRMWLoop/AtomicCASLoop` pseudo-insts expanded at
emit into the ldaxr/stlxr loops with fixed regs x24–x28 exactly as Cranelift's
`inst/emit.rs` does (has_lse=0, cg_clif's flags), `CSetm` (csinv), `Fence` (dmb ish);
regalloc fixed uses/defs (x25/x26 in, x27+scratch out) and clobbers; encoders checked against
llvm-mc; `Clif.run` semantics already exist. TLS `tls_value` (elf_gd) — parser rejects TLS
globals (Parse.lean:383); rules `elf_tls_get_addr` exist; probed only if a real fallback appears.
