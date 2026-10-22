import FV.E2E.StockDivFixtures
import FV.E2E.CompiledSemanticNI
import FV.Backend.LinearScan
import FV.Backend.Lowering.StockScalarNI
namespace E2E.StockDivNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def checks (config : Configuration) (op : Clif.DivOp) (cleanup : Bool) : Bool :=
  lowerScopeB (function config op) && dominatedB (function config op) && sigAbiOk (function config op).sig &&
  match Stock.lower (function config op) with
  | .error _ => false
  | .ok result =>
    !lowerCheck (function config op) result.code &&
    DivBoundary.check (function config op).sig result.code &&
    Stock.Scalar.check (function config op) result.code && SemanticNI.check (function config op) result.code &&
    (match Stock.Scalar.lowerValidated (function config op) with
      | .error _ => false
      | .ok vc => decide (vc = result.code)) &&
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

private def grid : Bool := configurations.all fun config => operations.all fun op => checks config op false && checks config op true
-- witness: native_decide (forty-eight fixed actual pipeline configurations only)
theorem checks_true : grid = true := by native_decide
/-- Actual checked/allocated/emitted artifacts inhabit the complete division
semantic domain in every ABI and cleanup mode, beyond the legacy checker. -/
theorem compiled_exists (config : Configuration) (op : Clif.DivOp) (cleanup : Bool) :
    Stock.Scalar.Domain (function config op) ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage (function config op) cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI (function config op) 0 result.code vcp rf af fa fb ∧
      Stock.Scalar.lowerValidated (function config op) = .ok result.code ∧
      DivBoundary.check (function config op).sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp ∧
      lowerCheck (function config op) result.code = false := by
  have h : checks config op cleanup = true := by
    have both := List.all_eq_true.mp checks_true config (by cases config <;> simp [configurations])
    have both := List.all_eq_true.mp both op (by cases op <;> simp [operations])
    simp only [Bool.and_eq_true] at both
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simp only [checks,Bool.and_eq_true] at h
  obtain ⟨⟨⟨scope,dominated⟩,abi⟩,h⟩ := h
  have domain : Stock.Scalar.Domain (function config op) :=
    Stock.Scalar.domain_of_single_div (lowerScope_of scope) (dominated_of dominated) abi
      (b := (function config op).blocks[0]!) rfl (stm := ⟨[100],.div op (valueType config) 1 8⟩) rfl rfl rfl rfl (by rfl)
  refine ⟨domain,?_⟩
  cases lowered : Stock.lower (function config op) with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨legacy,reads⟩,scalar⟩,paired⟩,actual⟩,h⟩ := h
    have actualLower : Stock.Scalar.lowerValidated (function config op) = .ok result.code := by
      cases observed : Stock.Scalar.lowerValidated (function config op) with
      | error message => simp [observed] at actual
      | ok vc =>
        simp only [observed,decide_eq_true_eq] at actual
        cases actual
        rfl
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
              have stage : CompiledStockArithmeticStage (function config op) cleanup 0 result vcp rf af fa fb :=
                ⟨lowered,prepared,prepOk,check,physical,emitted,layout⟩
              exact ⟨result,vcp,rf,af,fa,fb,stage,.scalarDiv domain rfl reads stage,
                actualLower,reads,allocated,(formsCoveredB_iff _ _).mp covered,legacy⟩

/-- Complete entry retains arbitrary source values and explicit slot address. -/
theorem source_entry (config : Configuration) (op : Clif.DivOp)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    ClifEntry (function config op) (arguments config input)
      ⟨frame config op input slot,[],Clif.Mem.empty⟩ := by
  cases config <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

end E2E.StockDivNIWitness
