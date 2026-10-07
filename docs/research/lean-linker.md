# A static linker in Lean (L2b, issue #10): survey, design, stages 1–2

docs/TO-PROVE.md §3 L2b. Today rust-lld links every executable; the crate theorem takes the
linker's facts `linkerOkB I` (`FV/E2E/LinkScopeDefs.lean`) and the binary theorems take `BinOk`
(`FV/E2E/BinCheck.lean`), both decided per crate by `native_decide`. This note surveys what
rust-lld links, chooses a design, and records stages 1 and 2 (implemented, proven, tested).

## 1. How `cargo fv` links today

* **Per codegen unit** (`rust/crates/cargo-fv/src/pipeline.rs`, `process_in`): every function
  of cg_clif's object is compiled by `lean-backend` into `o/f<i>.o`; `ld -r` of those gives
  `lean.o` (renamed symbols, one `__fvlean$<sym>` marker per function); cg_clif's object gets
  its locals that our code uses renamed to unique globals and its copies of our functions
  weakened; `ld -r --unique cg lean` merges the two (our strong definitions win), the renamed
  symbols are localised again, and the merged object replaces the unit's `.rcgu.o` (also inside
  rlibs, `wrapper.rs` `process_rlib`).
* **Per executable** (`wrapper.rs` `linker_main`, rustc runs `fv-rustc` as its linker): rust-lld
  `-flavor gnu` with rustc's arguments plus `--no-relax` (lld keeps `adrp`+`add`/`adrp`+`ldr`
  as emitted) and `-Map`. rustc's arguments (survey crate `a_arith`, test `values`):
  `crt1.o crti.o crtbegin.o symbols.o <unit>.rcgu.o… --as-needed -Bstatic libtest… liba_arith…
  libstd… libpanic_unwind… libobject… libmemchr… libaddr2line… libgimli… libcfg_if…
  librustc_demangle… libstd_detect… libhashbrown… libminiz_oxide… libadler2… libunwind…
  -lunwind liblibc… -lc liballoc… libcore… libcompiler_builtins… --eh-frame-hdr -z noexecstack
  --gc-sections -static -z relro -z now crtend.o crtn.o` — a static, non-PIE `ET_EXEC`
  (no `PT_DYNAMIC`/`PT_INTERP`, no dynamic relocations).
* **After the build**: the binary check (`bincheck.rs`): `cargo fv link-proof` (the link map's
  addresses, `FV/E2E/LinkCheck.lean` `LinkInput`) and `lake exe link-check` (`okB`, `BinOk`).

## 2. Survey: the link inputs of one executable

Survey executable: `a_arith`'s `values` test (`examples/survey`, `cargo fv test -p a_arith
--keep-temps`; 493 Lean-compiled functions, 2143 functions in all). Counts from the lld map's
kept input sections and `llvm-readelf -r` of the extracted members (script:
`/tmp/lean-linker_survey.py` at the time; reproducible from the map).

**Inputs kept** (after `--gc-sections`): 346 objects/members — musl `libc.a` 286 members,
`compiler_builtins` 35, Rust sysroot rlib members 13 (std, core, alloc, test, getopts,
rustc_demangle, gimli, addr2line, object, hashbrown, miniz_oxide, adler2, panic_unwind),
`libunwind.a` 5, crt objects 4 (`crt1.o crti.o crtbegin.o crtn.o`), the crate's objects 2
(the merged unit and the allocator-shim unit), rustc's `symbols.o`, plus lld's synthesized
sections (`.got`, `.eh_frame_hdr`, merged `.rodata.str*`/`.rodata.cst*`).

**Output sections** (bytes): `.rodata` 0x16714, `.gcc_except_table` 0x6940, `.eh_frame_hdr`
0x3af4, `.eh_frame` 0x16044, `.text` 0xb2ea8, `.init`/`.fini` 0x10 each, `.tdata` 0x48,
`.tbss` 0x48, `.fini_array` 0x8, `.init_array` 0x18, `.data.rel.ro` 0x9bb8, `.got` 0x1378
(623 slots), `.relro_padding`, `.data` 0xb78, `.bss` 0x1889; debug sections ~3.9 MB
(`.debug_info/abbrev/aranges/ranges/line/str/frame/loc`), `.symtab`/`.strtab`. Four `PT_LOAD`
(R: rodata+eh; R E: text/init/fini; RW relro: tdata…got; RW: data/bss), `PT_TLS`,
`PT_GNU_RELRO`, `PT_GNU_EH_FRAME`, `PT_GNU_STACK`.

**Relocations applied** (in kept allocated sections; debug sections add 153,577 `ABS64` and
80,616 `ABS32`, which a linker may drop with the debug info):

| type | count | where |
| --- | ---: | --- |
| `R_AARCH64_CALL26` | 12,103 | `.text` |
| `R_AARCH64_PREL32` | 3,936 | `.eh_frame` 3,921, `.rodata` 15 |
| `R_AARCH64_ADR_PREL_PG_HI21` | 3,815 | `.text` |
| `R_AARCH64_ADD_ABS_LO12_NC` | 3,643 | `.text` |
| `R_AARCH64_ABS64` | 2,133 | `.data.rel.ro` 2,115, `.data` 14, `.init_array` 3, `.fini_array` 1 |
| `R_AARCH64_ADR_GOT_PAGE` | 2,100 | `.text` |
| `R_AARCH64_LD64_GOT_LO12_NC` | 2,096 | `.text` |
| `R_AARCH64_PREL64` | 651 | `.eh_frame` |
| `R_AARCH64_JUMP26` | 557 | `.text` |
| `R_AARCH64_LDST8_ABS_LO12_NC` | 240 | `.text` |
| `R_AARCH64_LDST64_ABS_LO12_NC` | 107 | `.text` |
| `R_AARCH64_TLSDESC_ADR_PAGE21`/`LD64_LO12`/`ADD_LO12`/`CALL` | 45 each | `.text` (std's thread locals; lld relaxes them to local-exec) |
| `R_AARCH64_LDST128_ABS_LO12_NC` | 44 | `.text` |
| `R_AARCH64_LDST32_ABS_LO12_NC` | 33 | `.text` |
| `R_AARCH64_LDST16_ABS_LO12_NC` | 3 | `.text` |

18 allocated types (21 with the debug `ABS32`). By origin: Rust sysroot 17,653, the crate's
objects (cg_clif + Lean) 6,017 (`CALL26` 2,490, the GOT pair 1,608 each, `ABS64` 311), libunwind
2,019, musl 1,275, compiler_builtins 64, crt 41.

**The Lean backend's own code** (all 27 Lean-compiled codegen units of the nine survey crates,
`lean.o`): `CALL26` 5,568, `ADR_GOT_PAGE` 5,118, `LD64_GOT_LO12_NC` 5,118 in `.text`, and one
`PREL32` per FDE in `.eh_frame` (3,179). No `ADR_PREL_PG_HI21`/`ADD_ABS_LO12_NC` and no TLSDESC
in the survey (the backend can emit them: `Backend.RelocType`'s nine types). The Lean code has
no data of its own: it references cg_clif's data objects (`.Ldata*`, vtables) through the GOT.

**Section kinds a full linker must handle**: `.text*`, `.rodata*` (incl. `SHF_MERGE` strings and
constants), `.data`, `.data.rel.ro*`, `.bss`, `.tdata`/`.tbss` (TLS), `.init_array`/`.fini_array`
(ordering), `.init`/`.fini` (crti/crtn prologue/epilogue fragments), `.eh_frame` (CIE/FDE
records, `.eh_frame_hdr` binary-search table for libunwind via `PT_GNU_EH_FRAME`),
`.gcc_except_table` (LSDAs, referenced from FDEs), the synthesized `.got`, debug sections,
`.comment`, `.note.GNU-stack`; COMDAT groups in the sysroot objects; weak symbols (cg_clif's
copies of our functions).

**TLS**: one `PT_TLS` (tdata 0x48 + tbss 0x48, align 8); AArch64 TLS variant 1: thread pointer,
16-byte TCB, then the block (`E2E.Elf.tpOff`). Static musl sets it up in `__init_tls` from
`PT_TLS`. The 45 TLSDESC sequences become `movz x0`/`movk x0`/`nop`/`nop` (local exec).

**Entry/startup**: `e_entry` = `_start` (crt1.o) → `_start_c` → `__libc_start_main` (musl:
`__init_tls`, `_init` and `.init_array`) → `main` (rustc's, calling std's `lang_start`).

## 3. Design

What the theorems need of the linker (`linkerOkB`: `imgB`, `raCallB`, `raStarB`, `fits`,
`symInjB`, `symOkB`; `BinOk`: `Static`, `ArtOk` per function, `DataOk` per CLIF data object,
`SymsOk`) splits into facts about **the program part** (the Lean-compiled functions: where they
are, their relocated words) and facts about **the outside part** (headers, data objects of
cg_clif, the symbol table, the rest of the image).

**(a) Program part in Lean, outside part by rust-lld.** Lean places the program's functions
in one region by a placement function, relocates their words itself, and writes them into the
executable rust-lld linked around a placeholder of the region. `linkerOkB` becomes a theorem
(it is only about the placement and the compiled code); `ArtOk` becomes a theorem given
decidable facts about the outside file (`regionOkB`: the region is a read-only part of one
`PT_LOAD` segment, headers before it). `Static`, `DataOk`, `SymsOk` stay checks of the file
(the outside part's). Cost `[est]` before starting: ~0.3k lines of definitions, ~1.5k lines of
proofs, ~0.3k lines of Rust; risk: making rust-lld leave the region where Lean places it.

**(b) Full static linker in Lean.** Archive and ELF object reader, symbol resolution with
archive-member extraction, weak/COMDAT, section merging for the kinds above, `.eh_frame`
parsing and `.eh_frame_hdr`, the GOT, TLS layout and TLSDESC relaxation, the 18 relocation
types, `.init_array` order, an ELF writer (headers, segments, symbol table). Everything in
`BinOk` by construction (the writer's output read back by `FV/E2E/Elf.lean`), the outside part's
correctness reduced to "its bytes are its relocated input bytes". Cost `[est]`: 3–4k lines of
definitions, 2–4k lines of proofs (writer/reader round trip, relocation of the outside part),
performance work (std's rlibs are tens of MB; 240k debug relocations or dropping debug info).

**Decision: (a) first.** It removes both per-crate facts about the *program* (the part the
theorems are about) at a small fraction of (b)'s cost, keeps rust-lld for what the theorems do
not describe (std/musl/cg_clif code, unwind tables), and is a strict prefix of (b): the
placement, the relocation function and the region writer are reused when Lean also writes the
outside part. What stays checked is about the outside file only.

## 4. Stages 1 and 2 (implemented)

### Definitions (`FV/Link/`)

* `Layout.lean`: `offs`/`span` (functions consecutive, each followed by one zero gap word, so a
  call in a function's last word does not return into the next function); `LinkSpec` (the
  functions in placement order and their sizes in words, self-call aliases, the outside part's
  addresses `outside` and CLIF data objects `data`, the CLIF image's symbol names, the region's
  base `R`); `LinkSpec.input` (the crate-level `LinkInput` whose link map **is** the
  placement, with `syms` read from it and `raStar` the end of the region; a self-call alias's
  address is the gap word after its function); `placeOkB` (distinct names, one positive size
  per function, region nonzero, aligned, in the address space, no outside symbol in it);
  `sizesOkB` (the compiled code has the placement's sizes).
* `Reloc.lean`: `resolveWord` (each word from its own relocation: `bl` with the offset to
  `baseOf sym`; both page pairs as `adrp`+`add` of the target — the GOT pair too, which
  `PairOk.adrpAdd` accepts, so the program part needs no GOT; TLSDESC as
  `movz`/`movk`/`nop`/`nop` of `tpOff`), `relocsOkB` (the linker's check of the relocation
  shapes, partners and ranges), `regionBytes`.
* `Image.lean`: `patch`, `aliasOkB`/`aliasShapeB` (an alias's resolved words, raw words and call
  lines are its function's), **`leanLink S file0`**: the compiler's pipeline once, the linker's
  checks of its own output, the region's bytes written over the placeholder, then the checks of
  rust-lld's output (`regionOkB` on `file0`; `outsideOkB` on the written file: `hdrB`, `dataB`,
  `symsOkB`). A failing check is a link error, never a wrong executable.

### Theorems (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`)

* `Link.linkerOkB_place_alias (hp : S.placeOkB) (hr : pipeline ok) (hn : S.namesOkB …)
  (hs : S.sizesOkB …) (ha : aliasShapeB …) : linkerOkB S.input = true` — every conjunct by construction, self-call
  aliases included (`FV/Link/LayoutProof.lean`: `imgB_of`, the alias at its function's base with
  the same words; `raCallB` through `raOkB`'s shared-code case, `lineOffset_callShape`;
  `symInjB` with the alias at the gap word). `Link.linkerOkB_place` (no aliases) is a corollary.
* `Link.leanLink_linkerOk (h : leanLink S file0 = .ok file) : linkerOkB S.input = true`.
* `Link.artOk_of_image` (`RelocProof.lean`): resolved words in the file ⇒ `ArtOk`.
* `Link.leanLink_code (h) : ∀ e ∈ tabOf S.input.resultsT, ArtOk S.input file e.2`,
  `Link.leanLink_static'` (no premise) and **`Link.binOk_leanLink (h) : BinOk S.input S.data
  file`** (no premise; `OutsideProof.lean`, `Correct.lean`): `S.input`'s pipeline is the
  compiler's (`LinkInput.fallback`, so `S.input.results = S.input.resultsT`, the code the
  executable runs); stage 1's `leanLink_static`, `binOkT_leanLink` (with the outside facts as
  premises) are kept.
* `Link.crate_correct_leanLink (hD : SpillDefinedHyp) (hin : InScopeP S.input) (h : leanLink S
  file0 = .ok file) : CrateStmtT S.input n` — the crate theorem without `linkerOkB` (its axioms
  are `crate_correct_inScope`'s; `InScopeP` includes `entryParamsB` since #82, without which
  `SpillDefinedHyp` was false), and `Link.crate_correct_leanLink_lower (hM : LowerDefinedHyp)`
  (`crate_correct_inScope_lower`).
* Non-vacuity: `crate-proofs/Crates/LeanLinkWitness.lean` — `leanLink` succeeds on `a_arith`'s
  58 functions with a placeholder executable (one segment and a symbol table, `native_decide`),
  `InScopeP` of the placed input, instances of `crate_correct_leanLink`,
  `crate_correct_leanLink_lower`, `leanLink_code` and `binOk_leanLink`.

**Which facts are proven and which are checks of rust-lld's output.** Proven by construction
for every successful `leanLink`: `linkerOkB` (all of it) and the code part of `BinOk`
(`ArtOk`). Decided by `leanLink` on the file rust-lld wrote (`regionOkB`, `outsideOkB`; one
named check, no hypothesis left in `binOk_leanLink`): the headers (`Static`), cg_clif's data
objects (`DataOk`: the data belongs to cg_clif's code and is shared with it, laid out and
relocated by rust-lld), the symbol table (`SymsOk`, which for the program's functions is that
rust-lld put them at their placement: the outside part calls them through those symbols), and
that the region is a read-only part of one segment. They become theorems only when Lean writes
those bytes too (design (b)).

### The executable path: `cargo fv --lean-link`

* Codegen units: cg_clif's object with our functions weak and the renamed symbols global (no
  merge); `lean.o` stays in the work directory, each function followed by a zero gap word
  (`gap_object`), so `ld -r` lays it out as `Link.offs` does. Only verified functions enter the
  region: an unverified one keeps cg_clif's code (fallback, reason "unverified (…): cg_clif's
  code kept under --lean-link"), as does a self-calling function that takes its own address (the
  self-call alias's address in the theorem's link map is fresh, the executable's is the
  function's; one function of `examples/deps`, `foldhash`'s seed).
* At the executable's link (`leanlink.rs`): the work directories of the linked units (own
  objects, rlib members), by object name; `ld -r` of their `lean.o` → one object with section
  `.text.fvlean` (the region, `__fvlean_start`, strong definitions, the FDEs), and its functions'
  sizes (`sizes.txt`, from the object's symbols); rust-lld links everything with it
  (`-u __fvlean_start`); `cargo fv link-proof --cgus … --no-check` writes the Lean linker's
  input; `lake exe lean-link DIR SIZES` (`FVTest/Link/LeanLinkMain.lean`) builds the
  `LinkSpec`, runs `Link.leanLink` and writes the result over the executable.
* The usual binary check then runs on the patched executable (an independent check).
* Results:
  - all nine survey crates (`cd examples/survey && cargo fv test --lean-link`): 18 executables,
    27 to 493 functions each, every region written by `Link.leanLink`, the binary check verifies
    18 of 18, all 53 tests pass (as without `--lean-link`); the GOT pairs are `adrp`+`add`;
  - `examples/fv-demo` (with the unwinding cg_clif, `FV_CG_CLIF`): 458 and 882 functions with one
    self-call alias each, all 19 tests pass (unwinding through the region's code); the binary
    check's result is the one without `--lean-link` (1 of 2: 72 functions of the test harness
    fail `indScope`, as in the default build);
  - `examples/deps` (`cargo fv build --bin deps-demo --lean-link`): 17,090 functions (21 self-call
    aliases, 23,945 data objects), region 3.9 MB, written by `Link.leanLink`; the program runs.
* Cost of `lean-link` on `deps-demo` (41,300 link-map names, 19.8 MB executable): 232 s at
  first, 16 s (1.3 GB) after: names given by the driver and checked (`namesOkB`: `S.names`
  re-parsed every function's CLIF at each use), a hash-set `nodupB`, one address map for the
  data check (`dataFastB`: `objB` looked the object's address up per byte), the pipeline in
  parallel tasks (`parResultsT`). The rest is the compiler's pipeline (one run per function)
  and the list lookups of `relocsOkB` (≈6 s).

## 5. What remains

1. **The outside part's facts** (`regionOkB`, `outsideOkB`: headers, cg_clif's data objects,
   the symbol table) are checks of rust-lld's output inside `leanLink`. They become theorems
   only with design (b): the ELF writer, the relocation types of §2's table, `.eh_frame_hdr`,
   TLS. Moving the program's data into the region does not help: the data objects are cg_clif's,
   shared with its code.
2. **Self-calling functions that take their own address**: outside the region (fallback); the
   theorem's alias model gives the alias a fresh address. Covering them needs the alias at the
   function's address in `LinkSys` (`symInj` would have to allow it).
3. **The binary theorem on the Lean linker's output**: done (L1, `Link.compileExe_correct`,
   `FV/Link/Exe.lean`; docs/contracts/e2e.md "The executable compiler"): the binary chain is
   stated for `I.results`, which with `fallback` are the compiler's; `leanLink` also checks the
   code map `codeMapB`, and its output has no GOT slot (`leanLink_gotSlot`).
