import FV.Link.RelocShape
import FV.E2E.SpillDefined
import FV.Link.DeadCleanupCompile
import FV.Link.DeadCleanupCodeMapProof
import FV.Link.DeadCleanupOutsideProof
namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf Backend LinkSpec

theorem pipeT_fb (f : Clif.Function) (k : Nat) (b b' : BitVec 64) (o : Lean.Json) :
    (getOk (pipeCleanupT f k b o)).fb = (getOk (pipeCleanupT f k b' o)).fb := by
  simp only [pipeCleanupT, bind, Except.bind, pure, Except.pure]
  cases lowerFunction f with
  | error => rfl
  | ok vc =>
    simp only
    cases prepare (Backend.DeadCleanup.prune vc) with
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
def sizesOf (S : LinkSpec) : List Nat :=
  S.funcs.map fun fi => (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size

theorem names_of {S : LinkSpec} (hn : S.names = S.funcs.map (·.func.name)) :
    S.namesOkB (tabOf S.inputCleanup.resultsCleanupT) = true := by
  simp only [namesOkB, tabOf, LinkInput.resultsCleanupT, inputCleanup_funcs, List.map_map,
    ← List.map_take, List.take_length, hn, Function.comp_def]
  exact decide_eq_true trivial

theorem sizes_of {S : LinkSpec} (hs : S.sizes = sizesOf S) :
    S.sizesOkB (tabOf S.inputCleanup.resultsCleanupT) = true := by
  simp only [sizesOkB, tabOf, LinkInput.resultsCleanupT, inputCleanup_funcs, List.map_map,
    ← List.map_take, List.take_length, hs, sizesOf]
  apply decide_eq_true
  apply List.map_congr_left
  intro fi _
  simp only [Function.comp_apply]
  rw [pipeT_fb]

/-- The compiler's pipeline accepts every function of an in-scope input. -/
theorem results_of {S : LinkSpec} (hin : InScopeP S.input0 = true) :
    S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true := by
  simp only [InScopeP, Bool.and_eq_true, List.all_eq_true] at hin
  rw [List.all_eq_true]
  intro e he
  obtain ⟨fi, hfi, rfl⟩ := List.mem_map.1 he
  have hsc := hin.2 fi.func (List.mem_map_of_mem hfi)
  obtain ⟨a, ha, -⟩ := pipeCleanupT_ok hsc spillDefinedHyp fi.k (BitVec.ofNat 64 (S.inputCleanup.baseOf fi.func.name))
    (raJ fi.ra fi.j)
  simp only [ha]
  rfl

/-- **`leanLink` succeeds** when its checks hold (each passed in). -/
theorem leanLink_total_checks {S : LinkSpec} {file0 : ByteArray}
    {phs : List Phdr} (hph : phdrs (fileRd file0) = some phs) (hp : S.placeOkB = true)
    (hr : S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true)
    (hnm : S.namesOkB (tabOf S.inputCleanup.resultsCleanupT) = true)
    (hsz : S.sizesOkB (tabOf S.inputCleanup.resultsCleanupT) = true)
    (hv : (tabOf S.input0.resultsCleanupT).all (fun e => relocsOkB S.inputCleanup (tpOff phs) e.2) = true)
    (hcm : codeMapB S.inputCleanup (tabOf S.input0.resultsCleanupT) = true)
    (hreg : regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true)
    (hout : outsideOkB S.inputCleanup S.data (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) =
      true) :
    leanLink S file0 = .ok (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) := by
  unfold leanLink
  rw [hph]
  dsimp only
  rw [parResultsCleanupT_eq]
  have e1 : (!S.placeOkB) = false := by simp [hp]
  have e2 : (!S.input0.resultsCleanupT.all (·.2.toBool)) = false := by simp only [Bool.not_eq_false']; exact hr
  have e3 : (!S.namesOkB (tabOf S.input0.resultsCleanupT)) = false := by simp only [Bool.not_eq_false']; exact hnm
  have e4 : (!S.sizesOkB (tabOf S.input0.resultsCleanupT)) = false := by simp only [Bool.not_eq_false']; exact hsz
  have e5 : (!(tabOf S.input0.resultsCleanupT).all (fun e =>
      relocsOkB (S.input0.withDepth S.input0.resultsCleanupT) (tpOff phs) e.2)) = false := by
    simp only [Bool.not_eq_false']; exact hv
  have e8 : (!codeMapB (S.input0.withDepth S.input0.resultsCleanupT) (tabOf S.input0.resultsCleanupT)) =
      false := by simp only [Bool.not_eq_false']; exact hcm
  have e9 : (!regionOkB file0 S.R (ByteArray.mk (regionBytes (S.input0.withDepth S.input0.resultsCleanupT)
      (tpOff phs) ((List.take S.funcs.length (tabOf S.input0.resultsCleanupT)).map (·.2))).toArray).size
      (offsetOf phs S.R)) = false := by simp only [Bool.not_eq_false']; exact hreg
  have e10 : (!outsideOkB (S.input0.withDepth S.input0.resultsCleanupT) S.data (patch file0
      (offsetOf phs S.R) (ByteArray.mk (regionBytes (S.input0.withDepth S.input0.resultsCleanupT)
      (tpOff phs) ((List.take S.funcs.length (tabOf S.input0.resultsCleanupT)).map (·.2))).toArray))) =
      false := by simp only [Bool.not_eq_false']; exact hout
  simp only [e1, e2, e3, e4, e5, e8, e9, e10, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- **`leanLink` succeeds** when its checks hold, from their causes (module doc). -/
theorem leanLink_total_of {S : LinkSpec} {file0 : ByteArray}
    {phs : List Phdr} (hph : phdrs (fileRd file0) = some phs) (hin : InScopeP S.input0 = true)
    (hp : S.placeOkB = true)
    (hn : S.names = S.funcs.map (·.func.name)) (hs : S.sizes = sizesOf S)
    (hshape : ∀ e ∈ tabOf S.inputCleanup.resultsCleanupT, relocShapesB e.2 = true)
    (hrange : ∀ e ∈ tabOf S.inputCleanup.resultsCleanupT, ∀ r ∈ e.2.fb.relocs,
      relocRangeB S.inputCleanup (tpOff phs) e.2 r = true)
    (hreg : regionOkB file0 S.R (regionOf S (tpOff phs)).size (offsetOf phs S.R) = true)
    (hout : outsideOkB S.inputCleanup S.data (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) =
      true) :
    leanLink S file0 = .ok (patch file0 (offsetOf phs S.R) (regionOf S (tpOff phs))) := by
  have hr := results_of hin
  have hnm := names_of hn
  have hsz := sizes_of hs
  have hv : (tabOf S.input0.resultsCleanupT).all (fun e => relocsOkB S.inputCleanup (tpOff phs) e.2) = true :=
    List.all_eq_true.2 fun e he => relocsOkB_of (hshape e he) (hrange e he)
  have hcm : codeMapB S.inputCleanup (tabOf S.input0.resultsCleanupT) = true := codeMap_place hp hr hnm hsz
  exact leanLink_total_checks hph hp hr hnm hsz hv hcm hreg hout


end Link.DeadCleanup
