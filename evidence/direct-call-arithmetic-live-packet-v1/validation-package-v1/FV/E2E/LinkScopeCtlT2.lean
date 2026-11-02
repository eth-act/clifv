import FV.E2E.LinkScopeInputT2
import FV.E2E.SpillCtlCheckT
import FV.Backend.Proof.IselShpTDriver
import FV.Backend.Proof.SpillInstCheckComplete

/-! # The control-form run-time checks proven on the strengthened typed scope `fnScopeInTB2`

The other two run-time checks of `fnScopeInTB`'s non-E branch (`lowerOutTB`) hold on every
function of `fnScopeInTB2`:

* `ctlSpillB_of_T2`: `Spill.ctlSpillB` of `lowerFunction g` (every control form meets
  `SpillInstOk`);
* `ctlInstsB_of_T2`: `ctlInstsB` of `prepare (lowerFunction g)` (every instruction meets
  `ctlInstOk` at its position; block 0 starts with `Args` and has a second instruction).

Both come from the typed control-shape analysis (`CovT.iselCtlHypT`, `IselShpT*`) with the
entry-block typing `entryClassOkB` (`Spill.ctlSpillHypT_of`, `E2E.ctlInsts_pipelineT`).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver

/-- The ABI condition of the end-to-end subset from `fnScopeInTB`'s signature checks. -/
theorem abiSigsOk_of_T {g : Clif.Function} (h : fnScopeInTB g = true) : Spill.AbiSigsOk g := by
  have p := fnScopeInT_parts h
  refine ⟨⟨p.2.2.2.1, fun e he => List.all_eq_true.mp p.2.2.2.2.1 e he⟩, fun s hs => ?_⟩
  have := List.all_eq_true.mp p.2.2.2.2.2.1 s hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

/-- The conjuncts of `fnScopeInTB2` the typed control-shape analysis needs. -/
theorem ctlParts_of_T2 {g : Clif.Function} (h : fnScopeInTB2 g = true) :
    dominatedB g = true ∧ LowerScopeT g ∧ Compile.storeTypedB g = true ∧
      Compile.selectTypedB g = true ∧ Spill.AbiSigsOk g ∧ EntryClassOk g := by
  obtain ⟨hT, hec, hsel⟩ := fnScopeInT2_parts h
  have p := fnScopeInT_parts hT
  exact ⟨p.2.2.2.2.2.2.2.2.2.2.1, lowerScopeT_of p.2.2.2.2.2.2.2.2.2.2.2.1, p.2.1, hsel,
    abiSigsOk_of_T hT, entryClassOk_of hec⟩

/-- **`ctlSpillB` holds on `fnScopeInTB2`.** -/
theorem ctlSpillB_of_T2 {g : Clif.Function} {vc : VCode} (h : fnScopeInTB2 g = true)
    (hl : lowerFunction g = .ok vc) : Spill.ctlSpillB vc = true :=
  let ⟨hdom, hs, hst, hsel, ha, hec⟩ := ctlParts_of_T2 h
  Spill.ctlSpillB_of (Spill.ctlSpillHypT_of CovT.iselCtlHypT hdom hs hst hsel ha hec hl)

/-- **`ctlInstsB` holds on `fnScopeInTB2`**: of `prepare`'s output of `lowerFunction`'s VCode. -/
theorem ctlInstsB_of_T2 {g : Clif.Function} {vc vcp : VCode} (h : fnScopeInTB2 g = true)
    (hl : lowerFunction g = .ok vc) (hp : prepare vc = .ok vcp) : ctlInstsB vcp = true :=
  let ⟨hdom, hs, hst, hsel, ha, hec⟩ := ctlParts_of_T2 h
  ctlInstsB_of (ctlInsts_pipelineT CovT.iselCtlHypT hdom hs hst hsel ha hec hl hp)

end E2E.LinkCheck
