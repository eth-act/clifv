# Contract: the frontend boundary (T7, #43, #221)

The executable theorems (`Link.DeadCleanup.compileExe_correct{,_peak,_source,_source_peak}`,
`Link.compileExe_correct{,…}`) are about the `Link.LinkSpec` they compile. This file states what
that `LinkSpec` is made from, which part of the way from rustc to it is **trusted**, and which part
is a Lean function with a theorem.

```
rustc + patched cg_clif ──► *.unopt.clif / *.opt.clif with their    (trusted: the frontend)
                            external-name tables, the object
clif-data-export ──► the object's data objects (`; data:`)          (trusted: object reading)
cargo fv merge  ──► linked names of renamed symbols (`fv-link.json`) (proposal, checked)
cargo fv link-proof ──► bundle.json (collects files and addresses)   (I/O only)
Front.readBundle ──► Front.Bundle                                     (I/O only: files read verbatim)
Front.parseUnit  ──► the decoded units                                (Lean, proven: T7c)
Front.buildSpec  ──► Link.LinkSpec                                    (Lean, proven: T7d)
Link.DeadCleanup.compileExe ──► executable                            (Lean, proven: L1, L1f)
```

## 1. The trusted boundary

**The single remaining frontend assumption.** The frontend bundle faithfully represents the
program cg_clif compiled, unit by unit: for every codegen unit, (a) each Lean-compiled function's
dump (`FnFile.dump`) is cg_clif's dump of the function it compiled — its text, and after it the
function's **external-name table** and the codegen unit's **declarations** of the names it uses,
which the patched cg_clif writes (§2); (b) the unit's `; data:` lines are the data objects of the
unit's object (bytes, writability, relocations as `%symbol±addend`); (c) the unit's `locals` are
exactly the object's local symbols (two units' local symbols of one name are different symbols; a
global name is one symbol across units). Everything after the bundle is computed by Lean
functions with theorems (§4), or is a proposal that is checked.

The assumption covers these tools, which produce the bundle's content (pinned: the nightly of
`docs/PINS.md`, the cg_clif sources of its rustc commit with
`scripts/patches/cg-clif-extnames.patch`, built by `scripts/build-cg-clif.sh`, this repository's
revision of the tools):

| Tool | What is trusted | Why it is not proven |
| --- | --- | --- |
| rustc + rustc_codegen_cranelift (patched) | the CLIF dumps (`*.unopt.clif`, after `FunctionBuilder::finalize`; `*.opt.clif`, after Cranelift's mid-end, the input of the retry of `pipeline.rs` `compile_one`), their external-name tables and declarations, and the object | out of scope (§1.3 of `docs/TO-PROVE.md`): the theorems are about the CLIF, not about Rust. The patch only prints what cg_clif's module already holds (`write_ext_names`, §2) |
| `clif-data-export` | the data objects' bytes and relocations, read from the object by symbol (`.LdataN` as `c_LdataN`); one `; data:` line per data symbol of the object | reading ELF; the binary check compares every data object the program reaches with the executable's bytes at its link-map address (`outsideOkB`, `dataB`) |
| `Clif.parseFile` and its combinators (`Front.Raw`) | the meaning of the CLIF text (`docs/contracts/clif.md`); the raw dump syntax adds only external names `uNS:IDX`/`userextnameJ`/`%Libcall`, signature references in `fnK` declarations and skipped source locations `@XXXX` | the specification of the input language |
| the object merge (`pipeline.rs`) | nothing for correctness: its names (`fv-link.json` `names`) are checked to be a scoping (`Front.scopingB`), its object surgery is checked by the linker's checks (`symsOkB`, `regionOkB`, `outsideOkB`) | — |

Not trusted any more:

* T7d (#222): the renaming of the CLIF to linked names, the data closure, the CLIF image's
  symbols, the construction of each `FnInput` (formerly `cargo fv link-proof`'s textual `%name`
  substitution, `rename_clif`, and its data walk in Rust).
* T7b (#221): which symbol each `gvN = symbol … userextnameJ`, each callee `fnK = u0:N` and the
  function itself denote. `clif-data-export` recovered them from the order of GOT/TLSDESC
  relocations in the object and of external names in the `.vcode` dump, which could not detect a
  consistent swap of two symbols of one kind; cg_clif now writes them (§2) and the order-based
  recovery is deleted (`gvmap`, `fnmap`, the `.vcode` pairing).
* T7c (#221): `normalize.py`'s decoding (`u0:N` → symbol, `userextnameJ` → symbol, libcalls,
  signature inlining, comments and source locations). It is deleted; `Front.decodeFn` decodes,
  with a theorem relating the decoded program to the dumps' (§4). The build-time decoding of
  every function `lean-backend` compiles is the same Lean function (`lake exe clif-decode`).

Execution of the Lean functions (Lean's compiler and runtime, file I/O) is trusted as for every
Lean tool of this repository (`docs/TO-PROVE.md` §1.3).

## 2. cg_clif's dumps with their external-name tables (T7b)

cg_clif names code and data by **module identities** of its codegen unit's module: `u0:N` is
`FuncId` N, `u1:N` `DataId` N; the module declares a symbol for each (`ModuleDeclarations`), and
the object binds the identity to that symbol. A dump writes the function's own name and its
callees as identities (`function u0:7(…)`, `fn0 = colocated u0:20 sig0`), its symbol global values
by an entry of the function's external-name table (`gv0 = symbol colocated userextname1`, entry 1
of `Function::params.user_named_funcs`), and libcalls by name (`fn1 = %Memcpy sig1`). The table
and the declarations are not in Cranelift's text; `scripts/patches/cg-clif-extnames.patch`
(applied by `scripts/build-cg-clif.sh`; `pretty_clif.rs` `write_ext_names`, called by
`write_clif_file` for both stages) appends them after the function:

```text
; clifv-extnames 1
; userextname0 = u0:20
; userextname1 = u1:1
; decl u0:7 func local "_RNxC1g12Hg5oL5R9JQdx"
; decl u0:20 func import "__rust_u128_mulo"
; decl u1:1 data local ro notls ".Ldata1"
; libcall %Memcpy "memcpy"
; end clifv-extnames
```

* `userextnameJ = uNS:IDX`: every entry of the function's table;
* `decl uNS:IDX func LINKAGE "SYMBOL"` / `decl uNS:IDX data LINKAGE rw|ro tls|notls "SYMBOL"`: the
  module's declaration of every identity the function names, its own included: linkage
  (`import`, `local`, `preemptible`, `hidden`, `export`), for data writability and
  thread-locality, and the linkage name (`.Lfn<hex>`/`.Ldata<hex>` for anonymous declarations),
  written with Rust's `{:?}`;
* `libcall %NAME "SYMBOL"`: every libcall the function declares, with the symbol
  `cranelift_module::default_libcall_names` gives it (the names `driver::aot::make_module` gives
  the object module).

`cargo fv` requires the patched cg_clif (`target/cg_clif/{unwind,abort}/…`, `FV_CG_CLIF`); a dump
without a table does not decode, and its function falls back to cg_clif's code with that reason.

## 3. The frontend bundle, format `clifv-frontend-bundle` version 2

`cargo fv link-proof` writes `DIR/bundle.json` (`rust/crates/cargo-fv/src/linkproof.rs`); it only
collects files and addresses, it rewrites no CLIF and no data. `Front.readBundle`
(`FV/Front/Read.lean`) reads it and the files it names; a missing field, file or malformed entry is
an error.

```json
{
  "format": "clifv-frontend-bundle",
  "version": 2,
  "exe": "<the executable rust-lld linked>",
  "map": "<its lld link map>",
  "units": [
    {
      "tag": "<the unit's work directory name, distinct across units>",
      "object": "<the unit's object file name>",
      "functions": [
        { "name": "<CLIF name>", "final": "<linked name>",
          "dump": "<path: cg_clif's dump of the function, the stage lean-backend compiled>",
          "ra": "<path: lean-regalloc's output for its decoding>" }
      ],
      "data": "<path: the unit's data.clif, its `; data:` lines (every data object of the object)>",
      "locals": [["<CLIF name>", "<object symbol>"]],
      "names": { "<CLIF name>": "<linked name>" },
      "local_addrs": [["<object symbol>", 1234]]
    }
  ],
  "symbols": [["<executable symbol defined once>", 1234]],
  "markers": [["<linked name>", 1234]],
  "skipped": [["<linked name>", "<why the function is not in the region>"]]
}
```

* `units`, in the Lean linker's placement order (`--cgus`); `functions`: the unit's Lean-compiled,
  verified functions with a unique `__fvlean$` marker in the link map, in the unit's order. A
  function's `dump` is a copy of cg_clif's file kept in the unit's work directory (`c.clif/`).
* `locals`: the object's local symbols (`pipeline.rs`, `fv-link.json` `locals`; `c_LdataN` is the
  CLIF name of `.LdataN`, `Front.clifName`). `names`: the merge's linked names (local symbols our
  code uses become `__fv_<tag>_<symbol>`, globalised). `local_addrs`: the link map's address of a
  local symbol in this unit's object (one address).
* `symbols`, `markers`, `skipped`, the `SIZES` file of `lean-link`: link-time facts, checked by the
  linker (`placeOkB`, `sizesOkB`, `symsOkB`, `outsideOkB`); `skipped` non-empty is an error.

Version 1 (#222) named the decoded file `normalize.py` wrote (`"clif"`); it is not read any more.

Unsupported (the build falls back to cg_clif's code before the bundle, or `buildSpec` rejects):
a dump that does not hold exactly one function named as the bundle says, or without a table; a
name with no declaration, of the wrong kind (a callee that is no function or libcall, a `symbol`
of a TLS object or `tls` of another one) or whose symbol is no CLIF name (`[A-Za-z0-9_]+`, after
`.Ldata` → `c_Ldata`); two declarations of one identity with different symbols in a unit; a data
object named like a declared external name; a reachable data object whose line does not parse
(`clif-data-export` writes `; data: %name unsupported: …` for an object it cannot describe
exactly: a relocation other than `R_AARCH64_ABS64`, overlapping ones, a section-relative target no
data object covers); linked names that are not a scoping (a global renamed, two local symbols with
one linked name, a local symbol named like a global).

## 4. What is proven

`FV/Front/Raw.lean` (reading and decoding), `FV/Front/Bundle.lean` (definitions),
`FV/Front/BundleProof.lean`, `FV/Front/RawProof.lean`, `FV/Front/Rename.lean`,
`FV/Front/RenameStep.lean`, `FV/Front/RenameRun.lean`, `FV/Front/Perm.lean`, `FV/Front/Exe.lean`,
`FV/Front/RawExe.lean`.

* **The decoding (T7c).** `Front.readDump` parses a dump (`Raw.rawFunction`: the CLIF parser's
  combinators with the raw names) into the function as written and its table; `Dump.raw` resolves
  `userextnameJ` through the table to the module identity it denotes. `Front.decodeFn ρ d`
  renames every name by the unit's declarations `ρ` (`unitTable`: identity or libcall ↦ the CLIF
  name of its declared symbol; one symbol per identity across the unit's functions), after
  checking that every name is declared, of the right kind and expressible.
  `Front.decodeFn_spec`: the decoded function **is** `d.raw.rename (lookupRen ρ)`.
  `Front.parseUnit` decodes every function of a unit; `parseUnit_raw`: the parsed unit's
  functions are its dumps' functions in module identities (`PCgu.raw`) renamed by the unit's
  declarations (`PCgu.ren`); `parseUnit_fix`: its data names are fixed by them.
* **The units' program is cg_clif's program (T7c).** `rawLink us sc` is the program of the
  units as cg_clif wrote them, under a naming `sc` of their names (module identities, libcalls,
  data names). `RawScopingOk us sc`: `sc` names two names alike exactly when cg_clif declared them
  as one symbol — the same declared symbol, in the same unit or global in both (the meaning of
  module identities in cranelift-module, defined without the decoding). **`rawLink_eq_link`**:
  for every such `sc`, `rawPull us sc` is a scoping of the decoded units and
  `link us (rawPull us sc) = rawLink us sc`. `raw_alpha`: such a naming's program is
  alpha-equivalent to the linked one; `rawScoping_of`, `rawLink_decl`: the declarations followed
  by any scoping are such a naming, and cg_clif's program under it is the decoded one.
* **The units' program (T7d).** A **scoping** of the units (`Front.ScopingOk us sc`) names, per
  unit `i`, every name the unit uses (`PCgu.idents`: its functions' and its data closure's) so
  that two names get the same name iff they are one symbol: the same name, in the same unit or
  global in both. `Front.link us sc` is the program of the units under `sc` (every function
  renamed by `Function.rename (sc i)`), `Front.linkData us sc` its data.
* **Alpha-equivalence.** `Front.link_alpha`: for any two scopings `sc₁`, `sc₂` there is a
  bijection of names `σ` (`Clif.Ren`, built from transpositions: `Ren.ofPairs`,
  `ofPairs_fwd_of_consistent`) with `σ (sc₁ i n) = sc₂ i n` and
  `link us sc₂ = (link us sc₁).rename σ.fwd` (and the data likewise). `Clif.runLoop_ren`: the run
  of a program renamed by `σ`, in the renamed environment (`Env.ren`: the outside function at a
  renamed name is the original at the original name), from the renamed state, is the original run
  with its memory's symbol table and slot oracle renamed (`Mem.ren`), up to the messages of `stuck`
  (`Outcome.erase`); corollaries for returns and traps, both directions. So the semantics of the
  units' program does not depend on the scoping chosen.
* **The `LinkSpec` is the units' program.** `Front.buildSpec_spec`: when `buildSpec b = .ok S`, the
  units parse, the linked names are a scoping (`scopingB_sound`), the functions' sources
  (`FnInput.src`, what the compiler's source theorems call the source program) are
  `(link us (finOf us)).funcs` in order (each `FnInput`'s text is the printed renamed function,
  checked to parse back to it), `S.data = linkData us (finOf us)`, and every program function whose
  address the program's CLIF (`addrNamesOf`) or a reachable data object takes is in `S.symNames`.
  `buildSpec_srcProg`: `S.input0.srcProg = link us (finOf us)`.
* **The data closure loses nothing.** `Front.data_complete`: every object of a unit's `; data:`
  lines reachable from its functions' names through relocations (`Front.Reach`) is in the parsed
  unit's data; `data_sound`: only the unit's objects are; `data_parses`: no reachable line fails
  to parse.
* **The executable refines the units' program (T7e).** `Front.bundle_correct_source`,
  `bundle_correct_source_peak` (the shipped compiler `Link.DeadCleanup.compileExe`),
  `bundle_correct_source_baseline`, `bundle_correct_source_peak_baseline` (`Link.compileExe`):
  for `buildSpec b = .ok S`, a successful compilation of `S`, any `σ` with
  `link us (finOf us) = (link us sc).rename σ.fwd` (`link_alpha`, for any scoping `sc`), an
  environment `E` of the outside code under `sc`'s names with `B.env = E.ren σ`: an outside call of
  the executable's code of `f` refines the run of **`link us sc`** from `f`'s entry under `E` — a
  return is the executable's return of the split results with the memory renamed to the linked
  names, a trap (of a source run without load/store traps) the same trap. The premises about the
  source run (`ClifEntry`, `MemBounded` of the reachable states, `NoMemTrap`, `DepthLe`) are stated
  on the units' program (`clifEntry_ren`, `bnd_ren`, `noMemTrap_ren`, `depthLe_ren`); the others are
  the compiler theorems'.
* **The executable refines cg_clif's program (T7b, T7c).** `Front.bundle_correct_raw`,
  `bundle_correct_raw_peak`, `bundle_correct_raw_baseline`, `bundle_correct_raw_peak_baseline`:
  the same, about the runs of **`rawLink us sc`** for any `sc` with `RawScopingOk us sc` — the
  functions as cg_clif's dumps wrote them, names as cg_clif's module declared them.
* **Witnesses** on the real codegen unit of the survey crate `g_u128`
  (`crate-proofs/Crates/FrontendBundleInput.lean`, generated from its `bundle.json`: cg_clif's
  dumps as the patched cg_clif wrote them), restricted to `wmul_u128` and its callee
  `wrapping_mul`, a local symbol of the unit that the merge linked under a new name: the
  pre-renaming program and the linked one are alpha-equivalent (`alpha`); the pre-renaming run of
  `wmul_u128(2^64+3, 5)` returns `5·2^64+15` and the executable returns `15, 5` in x0, x1:
  `Crates.FrontendBundleWitness.bundle_source_witness` (shipped compiler),
  `Crates.FrontendBundleWitnessPeak.bundle_source_peak_witness` (depth 1),
  `Crates.FrontendBundleWitnessBaseline.bundle_baseline_witness`, `…bundle_baseline_peak_witness`;
  `data_witness`: the whole unit parses and `c_Ldata4`, reached only through `c_Ldata3`'s
  relocation, is in its data closure. `Crates.FrontendBundleWitnessRaw`: in cg_clif's program the
  two functions are `u0:27` and `u0:3` (`raw_names`), the declarations' naming is a
  `RawScopingOk` naming (`scd_ok`), and `bundle_raw_witness` instantiates `bundle_correct_raw`
  with the same run.

`lake exe lean-link` and `lake exe link-check` build their input with `Front.buildSpec` /
`Front.assemble` from `bundle.json`. With the decoding in Lean, `cargo fv test --lean-link
--verified` (fv-demo: 2 executables; the survey: 18, also with `--panic-abort`) and `cargo fv test`
(fv-demo) give the same test results and reports as with `normalize.py`/`clif-data-export`'s
recovery, and executables identical in every allocated section.

## 5. What remains trusted, and why

* **cg_clif and its patch.** The dumps, their tables and the object are cg_clif's (§1). The
  patch prints the module's existing declarations; it is a trusted part of the frontend, like the
  rest of cg_clif. Proving it would mean proving cg_clif.
* **Object reading.** `clif-data-export` reads the data objects' bytes and relocations from the
  object; a wrong reading changes the supplied data image, which the binary check compares with
  the executable (`outsideOkB`). The data a program reaches is computed in Lean (`data_complete`).
* **The parser.** `Clif.parseFile`'s combinators and the raw syntax of `Front.Raw` are the
  specification of what the text means (§1).
* **Stage selection.** The dump in the bundle is the one whose decoding `lean-backend` compiled:
  the unoptimised dump, or the optimised one when the unoptimised code references a symbol
  cg_clif's object neither defines nor references (Cranelift's optimiser removed its use). The
  theorems are about that dump's function; no theorem relates the optimised dump to the
  unoptimised one.
