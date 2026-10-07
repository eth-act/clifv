import FV.Link.Compile
import FV.Link.CodeMapProof
import FV.Link.RelocShape
import FV.Link.OutsideProof
import FV.E2E.SpillDefined

/-! # The executable compiler succeeds on in-scope input (L1): `leanLink`'s side

`leanLink_total_of`: `leanLink` succeeds when its checks hold, each from a stated cause:

* the pipeline (`pipeT_ok` under `InScopeP`, definite assignment proven: `spillDefinedHyp`);
* the names and sizes: the driver's (`S.names`, `S.sizes`) are the CLIF functions' names and the
  compiled code's sizes (`pipeT_fb`: the code does not depend on the load address);
* the relocations: their shapes (`relocShapesB`, a property of the compiler's output) and their
  ranges (`relocRangeB`: the addresses chosen by the placement and by rust-lld are within the
  relocations' reach);
* aliases (`aliasOkB`, `aliasShapeB`) and the code map (`codeMap_place`): by construction for an
  alias-free spec (the scope limit: `S.aliasFns = []`);
* rust-lld's output: `regionOkB`, `outsideOkB` (checks of the bytes rust-lld wrote).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

/-- The compiled code does not depend on the load address. -/
theorem pipeT_fb (f : Clif.Function) (k : Nat) (b b' : BitVec 64) (o : Lean.Json) :
    (getOk (pipeT f k b o)).fb = (getOk (pipeT f k b' o)).fb := by
  simp only [pipeT, bind, Except.bind, pure, Except.pure]
  cases lowerFunction f with
  | error => rfl
  | ok vc =>
    simp only
    cases prepare vc with
    | error => rfl
    | ok vcp =>
      simp only
      cases lowerAllocReady vcp (raAnswer vcp o) with
      | error => rfl
      | ok af =>
        simp only
        cases emitFunc k af with
        | error => rfl
        | ok fa =>
          simp only
          cases fa.layout with
          | error => rfl
          | ok fb => rfl

/-- **The driver's sizes**: every placed function's compiled size (at any load address). -/
def LinkSpec.sizesOf (S : LinkSpec) : List Nat :=
  S.funcs.map fun fi => (getOk (pipeT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size

theorem names_of {S : LinkSpec} (hal : S.aliasFns = [])
    (hn : S.names = S.funcs.map (·.func.name)) : S.namesOkB (tabOf S.input.resultsT) = true := by
  simp only [namesOkB, tabOf, LinkInput.resultsT, input_funcs, hal, List.append_nil, List.map_map,
    List.take_of_length_le (by simp : (S.funcs.map _).length ≤ S.funcs.length), hn,
    Function.comp_def]
  exact decide_eq_true trivial

theorem sizes_of {S : LinkSpec} (hal : S.aliasFns = []) (hs : S.sizes = S.sizesOf) :
    S.sizesOkB (tabOf S.input.resultsT) = true := by
  simp only [sizesOkB, tabOf, LinkInput.resultsT, input_funcs, hal, List.append_nil, List.map_map,
    List.take_of_length_le (by simp : (S.funcs.map _).length ≤ S.funcs.length), hs, sizesOf]
  apply decide_eq_true
  apply List.map_congr_left
  intro fi _
  simp only [Function.comp_apply]
  rw [pipeT_fb]

/-- The compiler's pipeline accepts every function of an in-scope input. -/
theorem results_of {S : LinkSpec} (hin : InScopeP S.input0 = true) :
    S.input.resultsT.all (·.2.toBool) = true := by
  simp only [InScopeP, Bool.and_eq_true, List.all_eq_true] at hin
  rw [List.all_eq_true]
  intro e he
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 he
  have hsc := hin.2 fi.func (List.mem_map_of_mem hfi)
  obtain ⟨a, ha, -⟩ := pipeT_ok hsc spillDefinedHyp fi.k (BitVec.ofNat 64 (S.input.baseOf fi.func.name))
    (raJ fi.ra fi.j)
  simp only [ha]
  rfl

/-- **`leanLink` succeeds** when its checks hold, from their causes (module doc). -/
theorem leanLink_total_of {S : LinkSpec} {file0 : ByteArray}
    {phs : List Phdr} (hph : phdrs (fileRd file0) = some phs) (hin : InScopeP S.input0 = true)
    (hp : S.placeOkB = true) (hal : S.aliasFns = [])
    (hn : S.names = S.funcs.map (·.func.name)) (hs : S.sizes = S.sizesOf)
    (hshape : ∀ e ∈ tabOf S.input.resultsT, relocShapesB e.2 = true)
    (hrange : ∀ e ∈ tabOf S.input.resultsT, ∀ r ∈ e.2.fb.relocs,
      relocRangeB S.input (tpOff phs) e.2 r = true)
    (hreg : regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true)
    (hout : outsideOkB S.input S.data (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) =
      true) :
    leanLink S file0 = .ok (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) := by
  have hP := placeOk_of hp
  have haliases : S.aliases = [] := by
    have := hP.aliasFns
    rw [hal] at this
    exact List.map_eq_nil_iff.1 this.symm
  have hr := results_of hin
  have hnm := names_of hal hn
  have hsz := sizes_of hal hs
  have hv : (tabOf S.input0.resultsT).all (fun e => relocsOkB S.input (tpOff phs) e.2) = true :=
    List.all_eq_true.2 fun e he => relocsOkB_of (hshape e he) (hrange e he)
  have hao : aliasOkB S.input (tpOff phs) (tabOf S.input0.resultsT) = true := by
    simp [aliasOkB, haliases]
  have has : aliasShapeB S.input (tabOf S.input0.resultsT) = true := by
    simp [aliasShapeB, haliases]
  have hcm : codeMapB S.input (tabOf S.input0.resultsT) = true := codeMap_place hp hr hnm hsz hal
  unfold leanLink
  rw [hph]
  dsimp only
  rw [parResultsT_eq]
  have e1 : (!S.placeOkB) = false := by simp [hp]
  have e2 : (!S.input0.resultsT.all (·.2.toBool)) = false := by simp only [Bool.not_eq_false']; exact hr
  have e3 : (!S.namesOkB (tabOf S.input0.resultsT)) = false := by simp only [Bool.not_eq_false']; exact hnm
  have e4 : (!S.sizesOkB (tabOf S.input0.resultsT)) = false := by simp only [Bool.not_eq_false']; exact hsz
  have e5 : (!(tabOf S.input0.resultsT).all (fun e =>
      relocsOkB (S.input0.withDepth S.input0.resultsT) (tpOff phs) e.2)) = false := by
    simp only [Bool.not_eq_false']; exact hv
  have e6 : (!aliasOkB (S.input0.withDepth S.input0.resultsT) (tpOff phs)
      (tabOf S.input0.resultsT)) = false := by simp only [Bool.not_eq_false']; exact hao
  have e7 : (!aliasShapeB (S.input0.withDepth S.input0.resultsT) (tabOf S.input0.resultsT)) =
      false := by simp only [Bool.not_eq_false']; exact has
  have e8 : (!codeMapB (S.input0.withDepth S.input0.resultsT) (tabOf S.input0.resultsT)) =
      false := by simp only [Bool.not_eq_false']; exact hcm
  have e9 : (!regionOkB file0 S.R (ByteArray.mk (regionBytes (S.input0.withDepth S.input0.resultsT)
      (tpOff phs) ((List.take S.funcs.length (tabOf S.input0.resultsT)).map (·.2))).toArray).size
      (offsetOf phs S.R)) = false := by simp only [Bool.not_eq_false']; exact hreg
  have e10 : (!outsideOkB (S.input0.withDepth S.input0.resultsT) S.data (patch file0
      (offsetOf phs S.R) (ByteArray.mk (regionBytes (S.input0.withDepth S.input0.resultsT)
      (tpOff phs) ((List.take S.funcs.length (tabOf S.input0.resultsT)).map (·.2))).toArray))) =
      false := by simp only [Bool.not_eq_false']; exact hout
  simp only [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, Bool.false_eq_true, ↓reduceIte]
  rfl

end Link
