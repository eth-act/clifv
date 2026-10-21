import FV.E2E.StockArithmeticStageContract
import FV.Backend.Proof.LowerDecide
import FV.Backend.Proof.RegallocCover
import FV.Backend.LinearScan
import FV.Backend.Lowering.StockD0

namespace E2E.StockLogicalExtrWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Distinct shift operands, a consumed ninth ABI argument, unused parameters,
an explicit slot and a dead statement. Both original OR operand orders occur. -/
def function (config : Configuration) (mirrored : Bool) : Clif.Function :=
  let ty := valueType config
  {source "stock_logical_extr" config [] with
    sig := {
      params := List.replicate 9 ⟨ty,.none,.normal⟩
      returns := [⟨ty,.none,.normal⟩]
      callConv := convention config}
    slots := [(7,⟨8,some 8⟩)]
    blocks := [{
      id := 0
      params := (List.range 9).map (fun i => (i,ty))
      body := [⟨[9],.iconst ty (ty.width-1 : Nat)⟩,⟨[10],.iconst ty 1⟩,
        ⟨[11],.binary .ishl ty 1 9⟩,⟨[12],.binary .ushr ty 8 10⟩,
        ⟨[13],.binary .bor ty (if mirrored then 12 else 11) (if mirrored then 11 else 12)⟩,
        ⟨[14],.binary .bxor ty 0 2⟩]
      term := .ret [13]}]}
def selected (result : Stock.Result) (mirrored : Bool) : Bool :=
  result.schedule.any fun step => step.rules.contains
    (if mirrored then Isle.Aarch64.rule_lower_1507.id else Isle.Aarch64.rule_lower_1501.id)

private def checks (config : Configuration) (mirrored cleanup : Bool) : Bool :=
  lowerScopeB (function config mirrored) && dominatedB (function config mirrored) && sigAbiOk (function config mirrored).sig &&
  match Stock.lower (function config mirrored) with
  | .error _ => false
  | .ok result =>
    (!lowerCheck (function config mirrored) result.code && selected result mirrored) &&
    match Backend.prepare (Stock.Arithmetic.stage cleanup result.code) with
    | .error _ => false
    | .ok vcp =>
      prepCheck (Stock.Arithmetic.stage cleanup result.code) vcp &&
      match leanAlloc vcp with
      | .error _ => false
      | .ok rf =>
        (checkAlloc vcp rf).isOk &&
        match lowerRFunc vcp rf with
        | .error _ => false
        | .ok af =>
          match emitFunc 0 af with
          | .error _ => false
          | .ok fa => formsCoveredB ⟨fa.k,af.slotBase⟩ vcp && fa.layout.isOk


private def grid : Bool := configurations.all fun config =>
  [false,true].all fun mirrored => [false,true].all fun cleanup => checks config mirrored cleanup
-- witness: native_decide (24 fixed actual full-pipeline configurations only)
theorem checks_true : grid = true := by native_decide

/-- Real Stock EXTR programs pass both cleanup modes through checked Lean
allocation and emitted bytes in every existing integer ABI configuration. -/
theorem compiled_exists (config : Configuration) (mirrored cleanup : Bool) :
    LowerScope (function config mirrored) ∧ Dominated (function config mirrored) ∧
    sigAbiOk (function config mirrored).sig = true ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage (function config mirrored) cleanup 0 result vcp rf af fa fb ∧
      selected result mirrored = true ∧ leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp ∧
      lowerCheck (function config mirrored) result.code = false := by
  have h : checks config mirrored cleanup = true := by
    have allConfig := List.all_eq_true.mp checks_true config (by cases config <;> simp [configurations])
    have allMirror := List.all_eq_true.mp allConfig mirrored (by cases mirrored <;> simp)
    exact List.all_eq_true.mp allMirror cleanup (by cases cleanup <;> simp)
  simp only [checks,Bool.and_eq_true] at h
  obtain ⟨⟨⟨scope,dominated⟩,abi⟩,h⟩ := h
  refine ⟨lowerScope_of scope,dominated_of dominated,abi,?_⟩
  cases lowered : Stock.lower (function config mirrored) with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true'] at h
    obtain ⟨⟨legacy,selectedRoot⟩,h⟩ := h
    cases prepared : Backend.prepare (Stock.Arithmetic.stage cleanup result.code) with
    | error message => simp [prepared] at h
    | ok vcp =>
      simp only [prepared,Bool.and_eq_true] at h
      obtain ⟨prepOk,h⟩ := h
      cases allocated : leanAlloc vcp with
      | error message => simp [allocated] at h
      | ok rf =>
        simp only [allocated,Bool.and_eq_true] at h
        obtain ⟨checked,h⟩ := h
        cases physical : lowerRFunc vcp rf with
        | error message => simp [physical] at h
        | ok af =>
          cases emitted : emitFunc 0 af with
          | error message => simp [physical,emitted] at h
          | ok fa =>
            simp only [physical,emitted,Bool.and_eq_true] at h
            obtain ⟨covered,layoutOk⟩ := h
            cases layout : fa.layout with
            | error message => rw [layout] at layoutOk; change false = true at layoutOk; cases layoutOk
            | ok fb =>
              have check : checkAlloc vcp rf = .ok () := by
                cases check : checkAlloc vcp rf with
                | error message => rw [check] at checked; change false = true at checked; cases checked
                | ok value => cases value; rfl
              exact ⟨result,vcp,rf,af,fa,fb,
                ⟨lowered,prepared,prepOk,check,physical,emitted,layout⟩,
                selectedRoot,allocated,(formsCoveredB_iff _ _).mp covered,legacy⟩

end E2E.StockLogicalExtrWitness
