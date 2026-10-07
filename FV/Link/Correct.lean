import FV.Link.ImageProof
import FV.Link.OutsideProof
import FV.Link.LayoutProof
import FV.E2E.SpillDefined

/-! # The Lean linker's output is correct (L2b)

For `leanLink S file0 = .ok file`, the facts the crate statement and `BinOk` need come in two
kinds. `S.input`'s pipeline is the compiler's (`fallback`), so its results are `resultsT`
(`LinkSpec.input_results`) and `BinOk S.input` is about the code the compiler emits.

**By construction** (proven from the placement and the compiler's output, nothing read back):

* the linker's facts `linkerOkB S.input` (`LayoutProof.leanLink_linkerOk`): the link map is the
  placement, the functions do not overlap, the return addresses, the self-call aliases (whose
  code is their function's: `aliasOkB`, `aliasShapeB`);
* **`leanLink_code`**: every function of the compiler's table `tabOf S.input.resultsT` is in
  `file` (`ArtOk`): a placed function from the region's bytes (`ImageProof.region_words`; its
  name and size are the placement's by `namesOkB`, `sizesOkB`), an alias from its function's
  words at the same base (`aliasOkB`), both with the relocation checks `relocsOkB`
  (`RelocProof.artOk_of_image`).

**Checked on rust-lld's output** (rust-lld wrote those bytes, so `leanLink` decides them on the
file instead of proving them, and fails the link otherwise):

* `regionOkB` on `file0`: the headers lie before the region, which is read-only in one
  `PT_LOAD` segment at its file offset (so the written bytes are the loaded code, and the
  headers are unchanged: `ImageProof`);
* `outsideOkB` on `file` (`OutsideProof`): the headers (a static AArch64 executable, `hdrB`),
  cg_clif's data objects `S.data` at their link-map addresses with their resolved bytes
  (`dataB`), and the symbol table (`symsOkB`): every link-map name a symbol at its address — for
  the program's functions, that rust-lld put them at their placement, through which the outside
  part calls them.

Theorems:

* **`leanLink_static'`** (`OutsideProof`): `file` is static, no premise; `leanLink_static`: from
  `Static file0` (the headers are `file0`'s);
* **`binOk_leanLink`**: `BinOk S.input S.data file`, no premise (the code by construction, the
  rest from `outsideOkB`); `binOkT_leanLink`: `BinOk` for any `D` given `Static file0`,
  `DataOk`, `SymsOk`;
* **`crate_correct_leanLink`**: the crate statement of an in-scope input linked by `leanLink`
  (`crate_correct_inScope` with the linker's facts `leanLink_linkerOk`; `InScopeP` includes
  `entryParamsB`); `crate_correct_leanLink_lower` under `LowerDefinedHyp`
  (`crate_correct_inScope_lower`).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-- The placed functions' sizes are the placement's (`sizesOkB`). -/
theorem placedArts_sizes {S : LinkSpec} (hs : S.sizesOkB (tabOf S.input.resultsT) = true) :
    (placedArts S).map (·.fb.words.size) = S.sizes := by
  rw [List.map_map]
  exact of_decide_eq_true hs

/-- `leanLink`'s output holds every placed function's resolved words, read-only. -/
theorem leanLink_placed {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hp : S.placeOkB = true) (hr : S.input.resultsT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.input.resultsT) = true) (hs : S.sizesOkB (tabOf S.input.resultsT) = true)
    (hok : regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true)
    {i : Nat} (hi : i < S.funcs.length) {e : Clif.Function × Art}
    (he : (tabOf S.input.resultsT)[i]? = some e) :
    (∀ k < e.2.fb.words.size, ∀ j < 4,
      Elf.ro (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) (wAt e.2 (4 * k + j))) ∧
    (∀ k < e.2.fb.words.size,
      readN (loadMem (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs)))) 4 (wAt e.2 (4 * k)) =
        some (resolveWord S.input (tpOff phs) e.2 k)) := by
  have hP := placeOk_of hp
  obtain ⟨e', he', hb, -⟩ := tab_placed hp hr hn hs i hi
  rw [he, Option.some.injEq] at he'
  subst he'
  have hsz := placedArts_sizes hs
  have ha : (placedArts S)[i]? = some e.2 := by
    simp only [List.getElem?_map, List.getElem?_take, hi, ↓reduceIte, he, Option.map_some]
  refine region_words hok ?_ ha ?_
  · rw [hsz]
    have := hP.fits
    simp only [LinkSpec.size] at this
    omega
  · rw [hsz]
    exact hb

/-- **Every function of the compiler's table is in `leanLink`'s output**, read-only, as its
resolved words (`resolveWord` with the file's thread-pointer offsets `tp`), its relocations
passing the linker's checks. -/
theorem leanLink_words {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file) :
    ∃ tp : Nat → Option Nat, (∀ v, TpOff file v = tp v) ∧ ∀ e ∈ tabOf S.input.resultsT,
      relocsOkB S.input tp e.2 = true ∧
      (∀ k < e.2.fb.words.size, ∀ j < 4, Elf.ro file (wAt e.2 (4 * k + j))) ∧
      (∀ k < e.2.fb.words.size,
        readN (loadMem file) 4 (wAt e.2 (4 * k)) = some (resolveWord S.input tp e.2 k)) := by
  obtain ⟨phs, hph, hp, hr, hn, hs, hv, hal, -, -, hok, -, rfl⟩ := leanLink_spec h
  have hP := placeOk_of hp
  refine ⟨tpOff phs, tpOff_patch hok hph, fun e he => ⟨List.all_eq_true.1 hv e he, ?_⟩⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
  have hil : i < (tabOf S.input.resultsT).length := (List.getElem?_eq_some_iff.1 hi).1
  rw [tab_length] at hil
  by_cases hin : i < S.funcs.length
  · exact leanLink_placed hp hr hn hs hok hin hi
  · -- an alias: its function's words at its function's base
    obtain ⟨e', ef, he', ⟨i', hi', hef⟩, hb, hl⟩ :=
      tab_alias hp hr hn hs (i - S.funcs.length) (by omega)
    rw [show S.funcs.length + (i - S.funcs.length) = i by omega, hi, Option.some.injEq] at he'
    subst he'
    have hw := leanLink_placed hp hr hn hs hok hi' hef
    have hefm : ef ∈ tabOf S.input.resultsT := List.mem_of_getElem? hef
    have hpm := mem_of_lookup hl
    have hal' := List.all_eq_true.1 hal _ hpm
    simp only [find?_key (tab_names S hP hn) he, find?_key (tab_names S hP hn) hefm, Bool.and_eq_true,
      beq_iff_eq, List.all_eq_true, List.mem_range] at hal'
    obtain ⟨hsz, hres⟩ := hal'
    have hwAt : ∀ o, wAt e.2 o = wAt ef.2 o := fun o => by simp only [wAt, hb]
    refine ⟨fun k hk j hj => ?_, fun k hk => ?_⟩
    · rw [hwAt]; exact hw.1 k (hsz ▸ hk) j hj
    · rw [hwAt, hres k hk]; exact hw.2 k (hsz ▸ hk)

/-- **Every function of the compiler's table is in `leanLink`'s output** (`ArtOk`). -/
theorem leanLink_code {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file) :
    ∀ e ∈ tabOf S.input.resultsT, ArtOk S.input file e.2 := by
  obtain ⟨tp, htp, hw⟩ := leanLink_words h
  intro e he
  obtain ⟨hv, hro, himg⟩ := hw e he
  exact artOk_of_image hv htp hro himg

/-- **`leanLink`'s output is a static executable** when the outside part is. -/
theorem leanLink_static {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file)
    (hs : Static file0) : Static file := by
  obtain ⟨phs, -, -, -, -, -, -, -, -, -, hok, -, rfl⟩ := leanLink_spec h
  exact static_patch hok hs

/-- **`BinOk` of `leanLink`'s output**: the code by construction; the outside part's headers
(`Static file0`), data objects and symbols (`DataOk`, `SymsOk`) as hypotheses. -/
theorem binOkT_leanLink {S : LinkSpec} {D : List Clif.DataObject} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) (hs : Static file0) (hd : ∀ o ∈ D, DataOk S.input file o)
    (hy : SymsOk S.input file) : BinOk S.input D file :=
  ⟨leanLink_static h hs, S.input_results ▸ leanLink_code h, hd, hy⟩

/-- **`BinOk` of `leanLink`'s output**, no premise: the code by construction (`leanLink_code`),
the headers, data objects and symbols by `leanLink`'s checks of rust-lld's output
(`outsideOkB`). -/
theorem binOk_leanLink {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file) :
    BinOk S.input S.data file := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hout, -⟩ := leanLink_spec h
  exact ⟨leanLink_static' h, S.input_results ▸ leanLink_code h, outsideOkB_data hout,
    outsideOkB_syms hout⟩

/-- **The crate statement of an in-scope input linked by `leanLink`**: `crate_correct_inScope`
with the linker's facts of `leanLink`'s output (`leanLink_linkerOk`). -/
theorem crate_correct_leanLink (hD : SpillDefinedHyp) {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopeP S.input = true) (h : leanLink S file0 = .ok file) (n : String) :
    CrateStmtT S.input n :=
  crate_correct_inScope hD hin (leanLink_linkerOk h) n

/-- `crate_correct_leanLink` under definite assignment of `lowerFunction`'s VCode
(`LowerDefinedHyp`, from which `SpillDefinedHyp` follows: `crate_correct_inScope_lower`). -/
theorem crate_correct_leanLink_lower (hM : LowerDefinedHyp) {S : LinkSpec}
    {file0 file : ByteArray} (hin : InScopeP S.input = true) (h : leanLink S file0 = .ok file)
    (n : String) : CrateStmtT S.input n :=
  crate_correct_inScope_lower hM hin (leanLink_linkerOk h) n

end Link
