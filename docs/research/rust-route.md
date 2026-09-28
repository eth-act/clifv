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
| 4. `dyn`/fn pointers (`call_indirect`, `func_addr`) | **in progress (WIP branch, does not close)** — `Clif.run` supports both (`stepCallIndirect`, `func_addr` via `mem.symbols`); parser/printer handle `sigN`; the Lean backend lowers both via the exported ISLE rules (`rule_lower_2529`, `func_addr` → `load_ext_name`, `gen_call_ind_info`, `value_slice_unwrap`, `InstructionData.CallIndirect/FuncAddr` term data). Both flagged unverified: outside `Compile.functionE` (subset E), `lowerCheck` requires `f.sigDecls.isEmpty`, `CtxInv` gained an `instE` field, `LowerSim.DriverHyp` gained `noCI`/`subE`/`normExts`, `CallRuleOk` gained `ExternsNormal`. Step-3 sret call-site helpers (`sigRets`/`sigArgLocs` in `gen_call_*`) restored after the WIP had reverted them. **`FV.E2E` builds green; `FV.E2E.OptProven` does NOT yet**: `FV/Opt/Proof/SemSim.lean` `step_eq_lift` (lstep vs `Clif.step` diverge on `callIndirect`; needs a no-callIndirect hypothesis threaded to its 7 callers). Regression gates not yet re-run. |
| 5. Re-count | not started (new goal from owner: work the failure list — i128 next, then callee closure — until all 933 pass; not begun) |

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

### Regression gates after step 1 (Lean untouched, but recorded)

`scripts/lean-backend-filetests.sh`: corpus **114/114**, extrt **22/22**, runtests **3085
pass / 0 fail / 0 disagree**. `scripts/lean-backend-encode-check.sh`: **971 identical,
0 differ**. `lake exe lean-e2e-check`: **lowerCheck 913 accepted / 0 rejected, prepCheck
913 accepted, formsCoveredB 913 covered / 0 not covered**. All green.

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
