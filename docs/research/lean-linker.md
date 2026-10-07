# A static linker in Lean (L2b, issue #10): survey, design, stage 1

docs/TO-PROVE.md §3 L2b. Today rust-lld links every executable; the crate theorem takes the
linker's facts `linkerOkB I` (`FV/E2E/LinkScopeDefs.lean`) and the binary theorems take `BinOk`
(`FV/E2E/BinCheck.lean`), both decided per crate by `native_decide`. This note surveys what
rust-lld links, chooses a design, and records stage 1 (implemented, proven, tested).

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

## 4. Stage 1 (implemented)

### Definitions (`FV/Link/`)

* `Layout.lean`: `offs`/`span` (functions consecutive, each followed by one zero gap word, so a
  call in a function's last word does not return into the next function); `LinkSpec` (the
  functions in placement order, self-call aliases, the outside part's addresses `outside`, the
  CLIF image's symbol names, the region's base `R`); `LinkSpec.input` (the crate-level
  `LinkInput` whose link map **is** the placement, with `syms` read from it and `raStar` the end
  of the region); `placeOkB` (distinct names, region nonzero, aligned, in the address space, no
  outside symbol in it).
* `Reloc.lean`: `resolveWord` (each word from its own relocation: `bl` with the offset to
  `baseOf sym`; both page pairs as `adrp`+`add` of the target — the GOT pair too, which
  `PairOk.adrpAdd` accepts, so the program part needs no GOT; TLSDESC as
  `movz`/`movk`/`nop`/`nop` of `tpOff`), `relocsOkB` (the linker's check of the relocation
  shapes, partners and ranges), `regionBytes`.
* `Image.lean`: `regionOkB` (the outside file's facts), `patch`, **`leanLink S file0`**: the
  placement, the compiler's pipeline (`resultsT`), the checks, the region's bytes written over
  the placeholder. A failing check is a link error, never a wrong executable.

### Theorems (no `sorry`; axioms `propext`, `Classical.choice`, `Quot.sound`)

* `Link.linkerOkB_place (hp : S.placeOkB) (hr : pipeline ok) (hal : S.aliases = [])` :
  `linkerOkB S.input = true` — every conjunct by construction (`FV/Link/LayoutProof.lean`;
  `imgB_of`: no two words at one address, `call_ret_le` from `FnAsm.layout_word`).
* `Link.leanLink_linkerOk (h : leanLink S file0 = .ok file) : linkerOkB S.input = true`
  (with self-call aliases `leanLink` decides `linkerOkR` itself: the open case).
* `Link.artOk_of_image` (`RelocProof.lean`): resolved words in the file ⇒ `ArtOk`.
* `Link.leanLink_code (h) : ∀ e ∈ tabOf S.input.resultsT, ArtOk S.input file e.2`,
  `Link.leanLink_static`, `Link.BinOkT` (`BinOk` with the code of the compiler's pipeline,
  `resultsT`, which the executable runs) and `Link.binOkT_leanLink (h) (Static file0) (DataOk…)
  (SymsOk…)` (`ImageProof.lean`, `Correct.lean`).
* `Link.crate_correct_leanLink (hD : SpillDefinedHyp) (hin : InScopeP S.input) (h : leanLink S
  file0 = .ok file) : CrateStmtT S.input n` — the crate theorem without `linkerOkB` (its axioms
  are `crate_correct_inScope`'s; `InScopeP` includes `entryParamsB` since #82, without which
  `SpillDefinedHyp` was false), and `Link.crate_correct_leanLink_lower (hM : LowerDefinedHyp)`
  (`crate_correct_inScope_lower`).
* Non-vacuity: `crate-proofs/Crates/LeanLinkWitness.lean` — `leanLink` succeeds on `a_arith`'s
  58 functions with a placeholder executable (`native_decide`), `InScopeP` of the placed input,
  instances of `crate_correct_leanLink`, `crate_correct_leanLink_lower` and `leanLink_code`.

Sizes: definitions 300 lines, proofs 1,430 lines (`LayoutFacts` 351, `LayoutProof` 362,
`RelocProof` 132, `ImageProof` 387, `Correct` 200).

### The executable path: `cargo fv --lean-link`

* Codegen units: cg_clif's object with our functions weak and the renamed symbols global (no
  merge); `lean.o` stays in the work directory, each function followed by a zero gap word
  (`gap_object`), so `ld -r` lays it out as `Link.offs` does.
* At the executable's link (`leanlink.rs`): the work directories of the linked units (own
  objects, rlib members), by object name; `ld -r` of their `lean.o` → one object with section
  `.text.fvlean` (the region, `__fvlean_start`, strong definitions, the FDEs); rust-lld links
  everything with it (`-u __fvlean_start`); `cargo fv link-proof --cgus … --no-check` writes the
  Lean linker's input; `lake exe lean-link` (`FVTest/Link/LeanLinkMain.lean`) checks that rust-lld
  put every function at its placement (the outside part reaches the program through those
  symbols), runs `Link.leanLink` and writes the result over the executable.
* The usual binary check then runs on the patched executable (an independent check).
* Result (`a_arith`): both executables linked by `Link.leanLink` (66 and 493 functions, regions
  of 6,080 and 113,400 bytes); the binary check verifies both; all 17 tests pass (the
  `should_panic` ones unwind through the region's code). The GOT pairs are `adrp`+`add` in the
  executable. `lean-link` takes 18 s for the 493 functions (the pipeline runs several times).
* All nine survey crates (`cd examples/survey && cargo fv test --lean-link`): 18 executables,
  27 to 493 functions each (3,179 in all, no self-call alias), every region written by
  `Link.leanLink`, the binary check verifies 18 of 18, every test passes (the same counts as
  without `--lean-link`).

## 5. What remains

1. **Outside-part facts still decided per executable**: `regionOkB` (inside `leanLink`),
   `Static`, `DataOk` (the data objects are cg_clif's), `SymsOk` (rust-lld's symbol table), and
   that rust-lld put the functions at their placement (`lean-link`'s check). Next: move the
   program's CLIF data objects into the program part (Lean lays out `; data:` objects and
   resolves their `%sym+off` items, `ABS64` only) so `DataOk` is by construction; then (b) for
   the headers and the symbol table.
2. **Self-call aliases**: `linkerOkB_place` assumes none; `leanLink` decides `linkerOkR` when
   there are some (prove `raOkB`'s alias case and `imgB` with equal raw words).
3. **Unverified Lean-compiled functions**: `--lean-link` refuses them (they would be in the
   region without a theorem); place them after the verified ones or exclude them from the
   region.
4. **Input plumbing**: `lean-link` reads `link-proof`'s directory (link map, executable symbol
   table); give it the work directories directly and compute the pipeline once.
5. **(b)**: the outside part (§3), starting with the ELF writer and the relocation types of
   §2's table, `.eh_frame_hdr`, TLS.
