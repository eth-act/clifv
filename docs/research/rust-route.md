# Rust route: real Rust crates through the all-Lean CLIF → AArch64 compiler

Work log for the Rust route (`docs/research/rust-clif-survey.md` §"Post-v2" and
`docs/DEFERRED.md` "Rust route extras"). Worktree `../clifv-wt/rust-route`, branch
`agent/rust-route`. Survey corpus: 933 functions (9 crates × debug / release /
release-oc), dumped by `scripts/rust-clif/dump.sh` into `/tmp/rust-clif-survey/out`.

## Status

| Step | State |
| --- | --- |
| 1. Data objects from cg_clif | **done** — `rust/crates/clif-data-export` recovers every data object of the corpus (294/294 data-using functions, 721 objects, 23 049 bytes; 0 mismatches over 933 functions × 3 profiles). Directives + gv table emitted; wired into `normalize.py --gvmap --data-file` and `tools.sh`; smoke runs of constant-table/vtable readers pass under `Clif.run` and the Lean backend natively, agreeing with rustc/LLVM. |
| 2. Panic and mem* externs | **in progress** — freestanding runtime + `Clif.Env` semantics |
| 3. `sret` | not started (design: `ensure_struct_return_ptr_is_returned`, param in x8, returned in x0; flagged unverified) |
| 4. `dyn`/fn pointers (`call_indirect`, `func_addr`) | not started (design: sigN declarations on `Clif.Function`, function symbols in the link-time image, `func_addr` = `mem.symbols` lookup) |
| 5. Re-count | not started |

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
| debug | 454 | 152 | 365 | 14 843 |
| release | 239 | 56 | 142 | 3 255 |
| release-oc | 240 | 86 | 214 | 4 951 |
| **total** | **933** | **294** | **721** | **23 049** |

Per-function results are the union of all 27 crate×profile runs; the tool exits non-zero
on any mismatch, and there are none.

(The per-crate numbers are reproducible with `scripts/rust-clif/data-export.sh`; the tool
exits non-zero on any mismatch, and there are none: every `symbol_value` target of the
corpus is recovered, including the 4 debug vtables and the writable `i_alloc` objects.)

Outputs per crate×profile: `<crate>.data.clif` (`; data:` directives, bytes as hex,
pointers as `%sym±addend`) and `<crate>.gvmap.tsv` (`dump-file \t gvN \t %name`).

### Remaining step-1 work (tracked)

- [ ] (done in step (b)) wire into `normalize.py`/`tools.sh`/`smoke.sh` and prove the
      bytes end to end.
- `align=` is not emitted (the `Clif.Image` aligns every object to ≥16 and the
  intra-object offsets are preserved, so placement is value-correct); `tls` and
  imported statics are out of scope (none in the corpus).

<!-- STATUS-MARKER -->
