import FV.Link.ActualCompilerImage
import FV.Link.OutsideProof
import FV.Link.ImageProof

/-! Actual-output image facts. All byte-writer checks are inherited;
no source or layout condition is added to its successful-output theorem. -/
set_option autoImplicit false
namespace Link.ActualImageProof
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

abbrev inputFor (S : LinkSpec) (lower : Clif.Function → Except String VCode)
    (stage : VCode → VCode) : LinkInput := S.inputWithLowering lower stage
abbrev resultsFor (S : LinkSpec) (lower : Clif.Function → Except String VCode)
    (stage : VCode → VCode) : Res := S.input0.resultsWithLowering lower stage
abbrev artsFor (S : LinkSpec) (lower : Clif.Function → Except String VCode)
    (stage : VCode → VCode) : List Art :=
  ((tabOf (resultsFor S lower stage)).take S.funcs.length).map (·.2)
abbrev regionFor (S : LinkSpec) (lower : Clif.Function → Except String VCode)
    (stage : VCode → VCode) (tp : Nat → Option Nat) : ByteArray :=
  ByteArray.mk (regionBytes (inputFor S lower stage) tp (artsFor S lower stage)).toArray

theorem spec {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode} {file0 file : ByteArray} (h : leanLinkWithLowering S file0 lower stage = .ok file) :
    ∃ phs, phdrs (fileRd file0) = some phs ∧ S.placeOkB = true ∧
      (resultsFor S lower stage).all (·.2.toBool) = true ∧
      S.namesOkB (tabOf (resultsFor S lower stage)) = true ∧
      S.sizesOkB (tabOf (resultsFor S lower stage)) = true ∧
      (tabOf (resultsFor S lower stage)).all (fun e => relocsOkB (inputFor S lower stage) (tpOff phs) e.2) = true ∧
      codeMapB (inputFor S lower stage) (tabOf (resultsFor S lower stage)) = true ∧
      regionOkB file0 S.R (regionFor S lower stage (tpOff phs)).size (offsetOf phs S.R) = true ∧
      outsideOkB (inputFor S lower stage) S.data file = true ∧
      file = patch file0 (offsetOf phs S.R) (regionFor S lower stage (tpOff phs)) := by
  unfold leanLinkWithLowering leanLinkWithResults at h
  split at h
  · cases h
  rename_i phs hph
  dsimp only at h
  rw [parResultsWithLowering_eq] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hp hr hn hs hv hcm hok hout
  cases h
  exact ⟨phs, hph, of_not_not hp, of_not_not hr, of_not_not hn, of_not_not hs, of_not_not hv,
    of_not_not hcm, of_not_not hok, of_not_not hout, rfl⟩

/-- Actual-output successful linking establishes a static executable directly. -/
theorem static_of_success {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode} {file0 file : ByteArray}
    (h : leanLinkWithLowering S file0 lower stage = .ok file) : Static file := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hout, _⟩ := spec h
  exact outsideOkB_static hout

/-- The actual callback contributes exactly one result per input function. -/
theorem tab_length (S : LinkSpec) (lower : Clif.Function → Except String VCode)
    (stage : VCode → VCode) :
    (tabOf (resultsFor S lower stage)).length = S.funcs.length := by
  simp [resultsFor, tabOf, LinkInput.resultsWithLowering, LinkSpec.input0]

theorem names_getElem! {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode}
    (hn : S.namesOkB (tabOf (resultsFor S lower stage)) = true) {i : Nat}
    (hi : i < S.funcs.length) : S.names[i]! = S.funcs[i].func.name := by
  have hs' := congrArg (·[i]?) (of_decide_eq_true hn)
  simp only [resultsFor, tabOf, LinkInput.resultsWithLowering, LinkSpec.input0,
    List.map_map, List.getElem?_map, List.getElem?_take, hi, ite_true,
    List.getElem?_eq_getElem hi, Option.map_some, Function.comp_def] at hs'
  rw [getElem!_pos S.names i (List.getElem?_eq_some_iff.1 hs'.symm).1]
  exact Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hs'.symm)

theorem tab_entry {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode}
    (hr : (resultsFor S lower stage).all (·.2.toBool) = true) {i : Nat}
    (hi : i < S.funcs.length) :
    ∃ fi a, S.funcs[i]? = some fi ∧
      S.input0.pipeOfWithLowering lower stage fi = .ok a ∧
      (tabOf (resultsFor S lower stage))[i]? = some (fi.func, a) := by
  let fi := S.funcs[i]
  refine ⟨fi, getOk (S.input0.pipeOfWithLowering lower stage fi),
    List.getElem?_eq_getElem hi, ?_, ?_⟩
  · apply getOk_eq
    have hl' : i < (resultsFor S lower stage).length := by
      simpa [resultsFor, LinkInput.resultsWithLowering, LinkSpec.input0] using hi
    have := List.all_eq_true.1 hr _ (List.getElem_mem hl')
    simpa only [resultsFor, LinkInput.resultsWithLowering, List.getElem_map,
      LinkSpec.input0] using this
  · simp only [resultsFor, tabOf, LinkInput.resultsWithLowering, LinkSpec.input0,
      List.map_map, List.getElem?_map, List.getElem?_eq_getElem hi]
    rfl

theorem tab_placed {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode} (hp : S.placeOkB = true)
    (hr : (resultsFor S lower stage).all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf (resultsFor S lower stage)) = true)
    (hs : S.sizesOkB (tabOf (resultsFor S lower stage)) = true) :
    ∀ i < S.funcs.length, ∃ e, (tabOf (resultsFor S lower stage))[i]? = some e ∧
      e.2.base = BitVec.ofNat 64 (S.R + (offs S.sizes 0)[i]!) ∧
      e.2.fb.words.size = S.sizes[i]! ∧ e.1.name = S.names[i]! ∧
      e.2.fa.layout = .ok e.2.fb := by
  intro i hi
  have hP := placeOk_of hp
  obtain ⟨fi, a, hfi, ha, ht⟩ := tab_entry hr hi
  rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hfi
  subst hfi
  have hn := names_getElem! hn hi
  obtain ⟨_, _, _, _, hl, _, hb⟩ := LinkInput.pipeOfWithLowering_provenance ha
  refine ⟨_, ht, ?_, ?_, hn.symm, hl⟩
  · rw [hb, ← hn]
    change BitVec.ofNat 64 (S.input.baseOf S.names[i]!) = _
    rw [baseOf_name hP hi]
  · have hs' := congrArg (·[i]?) (of_decide_eq_true hs)
    simp only [List.getElem?_map, List.getElem?_take, hi, ite_true, ht, Option.map_some] at hs'
    have hi' : i < S.sizes.length := by rw [hP.sizesLen]; exact hi
    rw [getElem!_pos S.sizes i hi',
      ← Option.some.inj (hs'.trans (List.getElem?_eq_getElem hi'))]

theorem arts_sizes {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode} (hs : S.sizesOkB (tabOf (resultsFor S lower stage)) = true) :
    (artsFor S lower stage).map (·.fb.words.size) = S.sizes := by
  rw [List.map_map]
  exact of_decide_eq_true hs

/-- `leanLink`'s output holds every placed function's resolved words, read-only. -/
theorem placed_words {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode} {file0 : ByteArray} {phs : List Phdr}
    (hp : S.placeOkB = true) (hr : (resultsFor S lower stage).all (·.2.toBool) = true)
    (hn : S.namesOkB (tabOf (resultsFor S lower stage)) = true) (hs : S.sizesOkB (tabOf (resultsFor S lower stage)) = true)
    (hok : regionOkB file0 S.R (regionFor S lower stage (tpOff phs)).size (offsetOf phs S.R) = true)
    {i : Nat} (hi : i < S.funcs.length) {e : Clif.Function × Art}
    (he : (tabOf (resultsFor S lower stage))[i]? = some e) :
    (∀ k < e.2.fb.words.size, ∀ j < 4,
      Elf.ro (patch file0 (offsetOf phs S.R) (regionFor S lower stage (tpOff phs))) (wAt e.2 (4 * k + j))) ∧
    (∀ k < e.2.fb.words.size,
      readN (loadMem (patch file0 (offsetOf phs S.R) (regionFor S lower stage (tpOff phs)))) 4 (wAt e.2 (4 * k)) =
        some (resolveWord (inputFor S lower stage) (tpOff phs) e.2 k)) := by
  have hP := placeOk_of hp
  obtain ⟨e', he', hb, -⟩ := tab_placed hp hr hn hs i hi
  rw [he, Option.some.injEq] at he'
  subst he'
  have hsz := arts_sizes hs
  have ha : (artsFor S lower stage)[i]? = some e.2 := by
    simp only [artsFor, List.getElem?_map, List.getElem?_take, hi, ↓reduceIte, he, Option.map_some]
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
theorem words {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode} {file0 file : ByteArray} (h : leanLinkWithLowering S file0 lower stage = .ok file) :
    ∃ tp : Nat → Option Nat, (∀ v, TpOff file v = tp v) ∧ ∀ e ∈ tabOf (resultsFor S lower stage),
      relocsOkB (inputFor S lower stage) tp e.2 = true ∧
      (∀ k < e.2.fb.words.size, ∀ j < 4, Elf.ro file (wAt e.2 (4 * k + j))) ∧
      (∀ k < e.2.fb.words.size,
        readN (loadMem file) 4 (wAt e.2 (4 * k)) = some (resolveWord (inputFor S lower stage) tp e.2 k)) := by
  obtain ⟨phs, hph, hp, hr, hn, hs, hv, -, hok, -, rfl⟩ := spec h
  refine ⟨tpOff phs, tpOff_patch hok hph, fun e he => ⟨List.all_eq_true.1 hv e he, ?_⟩⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 he
  have hil : i < (tabOf (resultsFor S lower stage)).length := (List.getElem?_eq_some_iff.1 hi).1
  rw [tab_length] at hil
  exact placed_words hp hr hn hs hok hil hi

/-- **Every function of the compiler's table is in `leanLink`'s output** (`ArtOk`). -/
theorem code {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode} {file0 file : ByteArray} (h : leanLinkWithLowering S file0 lower stage = .ok file) :
    ∀ e ∈ tabOf (resultsFor S lower stage), ArtOk (inputFor S lower stage) file e.2 := by
  obtain ⟨tp, htp, hw⟩ := words h
  intro e he
  obtain ⟨hv, hro, himg⟩ := hw e he
  exact artOk_of_image hv htp hro himg


/-- The actual linked file contains exactly the actual compiler artifacts;
all outside-file properties come from the existing byte-writer checks. -/
theorem bin_ok {S : LinkSpec} {lower : Clif.Function → Except String VCode}
    {stage : VCode → VCode} {file0 file : ByteArray}
    (h : leanLinkWithLowering S file0 lower stage = .ok file) :
    BinOkWithResults (inputFor S lower stage) (resultsFor S lower stage) S.data file := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hout, _⟩ := spec h
  exact ⟨static_of_success h, code h, outsideOkB_data hout, outsideOkB_syms hout⟩

end Link.ActualImageProof
