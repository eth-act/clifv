# Contract: the frontend boundary (T7, #43)

The executable theorems (`Link.DeadCleanup.compileExe_correct{,_peak,_source,_source_peak}`,
`Link.compileExe_correct{,…}`) are about the `Link.LinkSpec` they compile. This file states what
that `LinkSpec` is made from, which part of the way from rustc to it is **trusted**, and which part
is a Lean function with a theorem.

```
rustc + cg_clif ──► *.unopt.clif / *.opt.clif, object, vcode         (trusted: the frontend)
clif-data-export ──► identities of gvs/callees, data objects (`; data:`) (trusted: recovery)
normalize.py    ──► one CLIF file per function, names resolved        (trusted: decoding)
cargo fv merge  ──► linked names of renamed symbols (`fv-link.json`)  (proposal, checked)
cargo fv link-proof ──► bundle.json (collects files and addresses)    (I/O only)
Front.readBundle ──► Front.Bundle                                      (I/O only: files read verbatim)
Front.buildSpec ──► Link.LinkSpec                                      (Lean, proven: T7d)
Link.DeadCleanup.compileExe ──► executable                             (Lean, proven: L1, L1f)
```

## 1. The trusted boundary (T7a)

**The single remaining frontend assumption.** The frontend bundle faithfully represents the
program cg_clif compiled, unit by unit: for every codegen unit, (a) each Lean-compiled function's
CLIF file (`FnFile.clif`, one function, parsed by `Clif.parseFile`) is the function cg_clif
compiled, with every name it uses — its own, its callees', its global values' symbols — being the
symbol of the unit's object that cg_clif bound it to; (b) the unit's `; data:` lines are the data
objects of the unit's object (bytes, alignment, writability, relocations as `%symbol±addend`);
(c) the unit's `locals` are exactly the object's local symbols (two units' local symbols of one
name are different symbols; a global name is one symbol across units). Everything after the
bundle is computed by Lean functions with theorems (§3), or is a proposal that is checked.

The assumption covers these tools, which produce the bundle's content (pinned: the nightly of
`docs/PINS.md`, `rustc-codegen-cranelift-preview` or the `scripts/build-cg-clif-unwind.sh` build
of the same commit, this repository's revision of the tools):

| Tool | What is trusted | Why it is not proven (yet) |
| --- | --- | --- |
| rustc + rustc_codegen_cranelift | the CLIF dumps (`*.unopt.clif`, after `FunctionBuilder::finalize`; `*.opt.clif`, after Cranelift's mid-end, the input of the missing-data retry, `pipeline.rs` `compile_one`) and the object | out of scope (§1.3 of `docs/TO-PROVE.md`): the theorems are about the CLIF, not about Rust |
| `clif-data-export` | the identity of every `gvN = symbol … userextnameJ` (the data or TLS symbol it denotes, `gvmap`) and of callees of other units (`fnmap`), recovered from the order of GOT/TLSDESC relocations in the object and of external names in the `.vcode` dump; the data objects' bytes and relocations, read from the object | the dumps do not print the function's external-name table or the module's declarations: the identities are not in the text (T7b, §4) |
| `normalize.py` | the decoding of cg_clif's dump text into the parser's syntax: `function u0:N` → `%symbol` (the `; symbol` comment), `fnK = u0:N sigM` → `%symbol(sig)` (symbol of a function of the unit, the quoted symbol of the comment, `fnmap`), libcalls `%Memcpy sigM` → `%memcpy(sig)`, `gvK = symbol … userextnameJ` → `%symbol` (`gvmap`), `sigN` renumbered per function and inlined into `fn` declarations, comments and `@XXXX` source locations dropped | a decoding of a text format whose names it does not contain (§4); its remaining rewrites are syntactic |
| `Clif.parseFile` | the meaning of the CLIF text (`docs/contracts/clif.md`) | the specification of the input language |
| the object merge (`pipeline.rs`) | nothing for correctness: its names (`fv-link.json` `names`) are checked to be a scoping (`Front.scopingB`), its object surgery is checked by the linker's checks (`symsOkB`, `regionOkB`, `outsideOkB`) | — |

Not trusted any more (T7d): the renaming of the CLIF to linked names, the data closure, the CLIF
image's symbols, the construction of each `FnInput` (formerly `cargo fv link-proof`'s textual
`%name` substitution, `rename_clif`, and its data walk in Rust).

Execution of the Lean functions (Lean's compiler and runtime, file I/O) is trusted as for every
Lean tool of this repository (`docs/TO-PROVE.md` §1.3).

## 2. The frontend bundle, format `clifv-frontend-bundle` version 1

`cargo fv link-proof` writes `DIR/bundle.json` (`rust/crates/cargo-fv/src/linkproof.rs`); it only
collects files and addresses, it rewrites no CLIF and no data. `Front.readBundle`
(`FV/Front/Read.lean`) reads it and the files it names; a missing field, file or malformed entry is
an error.

```json
{
  "format": "clifv-frontend-bundle",
  "version": 1,
  "exe": "<the executable rust-lld linked>",
  "map": "<its lld link map>",
  "units": [
    {
      "tag": "<the unit's work directory name, distinct across units>",
      "object": "<the unit's object file name>",
      "functions": [
        { "name": "<CLIF name>", "final": "<linked name>",
          "clif": "<path: the CLIF file lean-backend compiled, one function>",
          "ra": "<path: lean-regalloc's output for it>" }
      ],
      "data": "<path: the unit's data-unopt.clif, its `; data:` lines>",
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
  verified functions with a unique `__fvlean$` marker in the link map, in the unit's order.
* `locals`: the object's local symbols (`pipeline.rs`, `fv-link.json` `locals`; `c_LdataN` is the
  CLIF name of `.LdataN`). `names`: the merge's linked names (local symbols our code uses become
  `__fv_<tag>_<symbol>`, globalised). `local_addrs`: the link map's address of a local symbol in
  this unit's object (one address).
* `symbols`, `markers`, `skipped`, the `SIZES` file of `lean-link`: link-time facts, checked by the
  linker (`placeOkB`, `sizesOkB`, `symsOkB`, `outsideOkB`); `skipped` non-empty is an error.

Unsupported (the build falls back to cg_clif's code before the bundle, or `buildSpec` rejects):
a function file that does not hold exactly one function named as the bundle says; a reachable
data object whose line does not parse; linked names that are not a scoping (a global renamed, two
local symbols with one linked name, a local symbol named like a global).

## 3. What is proven (T7d, T7e)

`FV/Front/Bundle.lean` (definitions), `FV/Front/BundleProof.lean`, `FV/Front/Rename.lean`,
`FV/Front/RenameStep.lean`, `FV/Front/RenameRun.lean`, `FV/Front/Perm.lean`, `FV/Front/Exe.lean`.

* **The units' program.** `Front.parseUnit` parses a unit (`PCgu`). A **scoping** of the units
  (`Front.ScopingOk us sc`) names, per unit `i`, every name the unit uses (`PCgu.idents`: its
  functions' and its data closure's) so that two names get the same name iff they are one symbol:
  the same name, in the same unit or global in both. `Front.link us sc` is the program of the
  units under `sc` (every function renamed by `Function.rename (sc i)`), `Front.linkData us sc` its
  data.
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
* **Witnesses** on the real codegen unit of the survey crate `g_u128`
  (`crate-proofs/Crates/FrontendBundleInput.lean`, generated from its `bundle.json`), restricted to
  `wmul_u128` and its callee `wrapping_mul`, a local symbol of the unit that the merge linked as
  `__fv_<tag>_…`: the pre-renaming program (every name as the frontend wrote it, a scoping) and the
  linked one are alpha-equivalent (`alpha`); the pre-renaming run of `wmul_u128(2^64+3, 5)`
  returns `5·2^64+15` and the executable returns `15, 5` in x0, x1:
  `Crates.FrontendBundleWitness.bundle_source_witness` (shipped compiler),
  `Crates.FrontendBundleWitnessPeak.bundle_source_peak_witness` (depth 1),
  `Crates.FrontendBundleWitnessBaseline.bundle_baseline_witness`, `…bundle_baseline_peak_witness`;
  `data_witness`: the whole unit parses and `c_Ldata4`, reached only through `c_Ldata3`'s
  relocation, is in its data closure.

`lake exe lean-link` and `lake exe link-check` build their input with `Front.buildSpec` /
`Front.assemble` from `bundle.json`; `cargo fv --lean-link` executables are byte-identical to the
earlier text-renaming pipeline's (outside debug info, fv-demo and the survey).

## 4. What remains trusted, and why (T7b, T7c: #221)

* **Identities (T7b, not done).** cg_clif's dumps print `gvN = symbol colocated userextnameJ`
  without the function's external-name table, and `fnK = u0:N` for a function of another unit
  with an `Instance` comment but no symbol. The mapping exists only inside cg_clif (the function's
  `user_named_funcs`, the module's declarations). `clif-data-export` recovers it from the object's
  relocations and the `.vcode` dump in emission order, with count and consistency checks; a
  consistent permutation of two same-kind symbols would not be detected. Removing this needs a
  change of cg_clif (printing the external-name table and the module's declarations where the dump
  is written), i.e. a patched frontend build for every `cargo fv` user; not done.
* **The decoding (T7c, fallback).** Without those identities the raw dump has no semantics for its
  global values and foreign callees that a Lean decoder could be proven against: the
  correspondence would hold by definition of the recovered tables. `normalize.py` therefore stays
  the explicitly specified decoding (§1 table, its docstring), now with each function's `sigN`
  declarations resolved within that function. Its renumbering of `sigN` and the dropping of
  comments and source locations are syntactic; a misdecoded name or signature changes the program
  the theorems are about, not the theorems.
* **Stage selection.** The CLIF file in the bundle is the one `lean-backend` compiled: the
  unoptimised dump, or the optimised one on the missing-data retry. The theorems are about that
  file's function; no theorem relates the optimised dump to the unoptimised one.
