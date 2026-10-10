import FV.Link.DeadCleanupLayoutProof
import FV.Link.ImageProof
import FV.E2E.SpillDefined
import FV.E2E.DeadCleanupBinCheck
namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

theorem placedArts_sizes {S : LinkSpec} (hs : S.sizesOkB (tabOf S.inputCleanup.resultsCleanupT) = true) :
    (placedArts S).map (·.fb.words.size) = S.sizes := by
  rw [List.map_map]
  exact of_decide_eq_true hs

/-- `leanLink`'s output holds every placed function's resolved words, read-only. -/
theorem leanLink_placed {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hp : S.placeOkB = true) (hr : S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf S.inputCleanup.resultsCleanupT) = true) (hs : S.sizesOkB (tabOf S.inputCleanup.resultsCleanupT) = true)
    (hok : regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true)
    {i : Nat} (hi : i < S.funcs.length) {e : Clif.Function × Art}
    (he : (tabOf S.inputCleanup.resultsCleanupT)[i]? = some e) :
    (∀ k < e.2.fb.words.size, ∀ j < 4,
      Elf.ro (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) (wAt e.2 (4 * k + j))) ∧
    (∀ k < e.2.fb.words.size,
      readN (loadMem (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs)))) 4 (wAt e.2 (4 * k)) =
        some (resolveWord S.inputCleanup (tpOff phs) e.2 k)) := by
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
    ∃ tp : Nat → Option Nat, (∀ v, TpOff file v = tp v) ∧ ∀ e ∈ tabOf S.inputCleanup.resultsCleanupT,
      relocsOkB S.inputCleanup tp e.2 = true ∧
      (∀ k < e.2.fb.words.size, ∀ j < 4, Elf.ro file (wAt e.2 (4 * k + j))) ∧
      (∀ k < e.2.fb.words.size,
        readN (loadMem file) 4 (wAt e.2 (4 * k)) = some (resolveWord S.inputCleanup tp e.2 k)) := by
  obtain ⟨phs, hph, hp, hr, hn, hs, hv, -, hok, -, rfl⟩ := leanLink_spec h
  refine ⟨tpOff phs, tpOff_patch hok hph, fun e he => ⟨List.all_eq_true.1 hv e he, ?_⟩⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
  have hil : i < (tabOf S.inputCleanup.resultsCleanupT).length := (List.getElem?_eq_some_iff.1 hi).1
  rw [tab_length] at hil
  exact leanLink_placed hp hr hn hs hok hil hi

/-- **Every function of the compiler's table is in `leanLink`'s output** (`ArtOk`). -/
theorem leanLink_code {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file) :
    ∀ e ∈ tabOf S.inputCleanup.resultsCleanupT, ArtOk S.inputCleanup file e.2 := by
  obtain ⟨tp, htp, hw⟩ := leanLink_words h
  intro e he
  obtain ⟨hv, hro, himg⟩ := hw e he
  exact artOk_of_image hv htp hro himg

/-- **`leanLink`'s output is a static executable** when the outside part is. -/
theorem leanLink_static {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file)
    (hs : Static file0) : Static file := by
  obtain ⟨phs, -, -, -, -, -, -, -, hok, -, rfl⟩ := leanLink_spec h
  exact static_patch hok hs

/-- **`E2E.DeadCleanupBinCheck.BinOk` of `leanLink`'s output**: the code by construction; the outside part's headers
(`Static file0`), data objects and symbols (`DataOk`, `SymsOk`) as hypotheses. -/
theorem binOkT_leanLink {S : LinkSpec} {D : List Clif.DataObject} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) (hs : Static file0) (hd : ∀ o ∈ D, DataOk S.inputCleanup file o)
    (hy : SymsOk S.inputCleanup file) : E2E.DeadCleanupBinCheck.BinOk S.inputCleanup D file :=
  ⟨leanLink_static h hs, S.inputCleanup_results ▸ leanLink_code h, hd, hy⟩

/-- **`E2E.DeadCleanupBinCheck.BinOk` of `leanLink`'s output**, no premise: the code by construction (`leanLink_code`),
the headers, data objects and symbols by `leanLink`'s checks of rust-lld's output
(`outsideOkB`). -/
theorem binOk_leanLink {S : LinkSpec} {file0 file : ByteArray} (h : leanLink S file0 = .ok file) :
    E2E.DeadCleanupBinCheck.BinOk S.inputCleanup S.data file := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hout, -⟩ := leanLink_spec h
  exact ⟨leanLink_static' h, S.inputCleanup_results ▸ leanLink_code h, outsideOkB_data hout,
    outsideOkB_syms hout⟩

/-- **The crate statement of an in-scope input linked by `leanLink`**: `crate_correct_inScope`
with the linker's facts of `leanLink`'s output (`leanLink_linkerOk`). -/
theorem crate_correct_leanLink (hD : SpillDefinedHyp) {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopeP S.inputCleanup = true) (h : leanLink S file0 = .ok file) (n : String) :
    CrateStmtCleanupT S.inputCleanup n :=
  crate_correct_inScope_cleanup hD hin (leanLink_linkerOk h) n

/-- `crate_correct_leanLink` under definite assignment of `lowerFunction`'s VCode
(`LowerDefinedHyp`, from which `SpillDefinedHyp` follows: `crate_correct_inScope_lower`). -/
theorem crate_correct_leanLink_lower (hM : LowerDefinedHyp) {S : LinkSpec}
    {file0 file : ByteArray} (hin : InScopeP S.inputCleanup = true) (h : leanLink S file0 = .ok file)
    (n : String) : CrateStmtCleanupT S.inputCleanup n :=
  crate_correct_inScope_cleanup (spillDefinedHyp_of_lower hM) hin (leanLink_linkerOk h) n

/-- **The crate statement of an in-scope input linked by `leanLink`**, no open hypothesis
(`crate_correct_inScope_proven`: definite assignment proven). -/
theorem crate_correct_leanLink_proven {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopeP S.inputCleanup = true) (h : leanLink S file0 = .ok file) (n : String) :
    CrateStmtCleanupT S.inputCleanup n :=
  crate_correct_inScope_cleanup spillDefinedHyp hin (leanLink_linkerOk h) n


end Link.DeadCleanup
