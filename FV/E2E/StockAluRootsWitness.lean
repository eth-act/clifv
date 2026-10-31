import FV.E2E.StockAluRootsFixtures
import FV.E2E.StockHighMulWitness
import FV.E2E.StockScalarNI
import FV.E2E.CompiledSemanticNI
import FV.Backend.LinearScan
import FV.Backend.Lowering.StockD0

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace E2E.StockAluRootsWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def checks (config : Configuration) (cleanup : Bool) : Bool :=
  lowerScopeB (function config) && dominatedB (function config) && sigAbiOk (function config).sig &&
  match Stock.lower (function config) with
  | .error _ => false
  | .ok result =>
    !lowerCheck (function config) result.code &&
    ScalarBoundary.check (function config).sig result.code &&
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

private def grid : Bool := configurations.all fun config => checks config false && checks config true
-- witness: native_decide (twelve fixed actual pipeline configurations only)
theorem checks_true : grid = true := by native_decide
end E2E.StockAluRootsWitness



namespace E2E.StockAluRootsWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0

private theorem family (config : Configuration) :
    ∀ stm ∈ (function config).blocks[0]!.body, Stock.Proof.HighMulBody.Family stm.inst := by
  intro stm member
  change stm ∈ (E2E.StockHighMulNIWitness.function config).blocks[0]!.body ++ extraBody config at member
  rcases List.mem_append.mp member with old | alu
  · exact E2E.StockHighMulNIWitness.source_family config stm old
  · have checked : (extraBody config).all Backend.Stock.Scalar.highmulBodyEligible = true := by
      cases config <;> rfl
    exact Backend.Stock.Scalar.highmulBodyEligible_sound (List.all_eq_true.mp checked stm alu)

/-- Actual checked/allocated/emitted artifacts inhabit the complete mixed semantic domain in
every ABI and cleanup mode with all operand forms of the integer ALU roots. -/
theorem compiled_exists (config : Configuration) (cleanup : Bool) :
    Stock.Scalar.Domain (function config) ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage (function config) cleanup 0 result vcp rf af fa fb ∧
      ScalarBoundary.check (function config).sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp ∧
      lowerCheck (function config) result.code = false := by
  have h : checks config cleanup = true := by
    have both := List.all_eq_true.mp checks_true config (by cases config <;> simp [configurations])
    simp only [Bool.and_eq_true] at both
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simp only [checks,Bool.and_eq_true] at h
  obtain ⟨⟨⟨scope,dominated⟩,abi⟩,h⟩ := h
  have domain : Stock.Scalar.Domain (function config) :=
    Stock.Scalar.domain_of_highmul (lowerScope_of scope) (dominated_of dominated) abi
      (b := (function config).blocks[0]!) rfl (family config) (xs := [5119]) rfl (by rfl)
  refine ⟨domain,?_⟩
  cases lowered : Stock.lower (function config) with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true'] at h
    obtain ⟨⟨legacy,reads⟩,h⟩ := h
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
                reads,allocated,(formsCoveredB_iff _ _).mp covered,legacy⟩
end E2E.StockAluRootsWitness

namespace E2E.StockAluRootsWitness
/-- Every scalar add/sub/and/or/xor root and the fused multiply roots of the original
inventory (`stock_addsub_selected_rule_ids`, `LogicalComplete.selected_rule_ids`). -/
def aluRoots : List Nat :=
  [588,589,590,591,592,593,594,595,596,597,598,599,745,746,747,748,749,
   836,841,842,849,854,855,862,863,864,869,870]

def aluRootsCovered (result : Backend.Stock.Result) : Bool :=
  aluRoots.all (E2E.StockHighMulNIWitness.selectedRoots result).contains

private def classChecks (config : Backend.Stock.D0.Configuration) : Bool :=
  Backend.Stock.Scalar.sourceOk (function config) &&
  match Backend.Stock.lower (function config) with
  | .error _ => false
  | .ok result => Backend.Stock.Scalar.check (function config) result.code && aluRootsCovered result

-- witness: native_decide (six fixed actual source/provenance checks only)
theorem source_checks_true : Backend.Stock.D0.configurations.all classChecks = true := by native_decide

/-- Actual source inputs and outputs jointly inhabit both production scalar checks in every ABI. -/
theorem classifier_accepts (config : Backend.Stock.D0.Configuration) :
    ∃ result, Backend.Stock.lower (function config) = .ok result ∧
      Backend.Stock.Scalar.sourceOk (function config) = true ∧
      Backend.Stock.Scalar.check (function config) result.code = true := by
  have h := List.all_eq_true.mp source_checks_true config
    (by cases config <;> simp [Backend.Stock.D0.configurations])
  simp only [classChecks,Bool.and_eq_true] at h
  obtain ⟨source,h⟩ := h
  cases lowered : Backend.Stock.lower (function config) with
  | error message => simp [lowered] at h
  | ok result =>
    have both : Backend.Stock.Scalar.check (function config) result.code = true ∧
        aluRootsCovered result = true := by simpa only [lowered,Bool.and_eq_true] using h
    exact ⟨result,rfl,source,both.1⟩

/-- Every ABI selects all 28 scalar integer ALU roots in one production-class function. -/
theorem selected_roots_present (config : Backend.Stock.D0.Configuration) :
    ∃ result, Backend.Stock.lower (function config) = .ok result ∧
      ∀ id ∈ aluRoots, id ∈ E2E.StockHighMulNIWitness.selectedRoots result := by
  have h := List.all_eq_true.mp source_checks_true config
    (by cases config <;> simp [Backend.Stock.D0.configurations])
  simp only [classChecks,Bool.and_eq_true] at h
  obtain ⟨source,h⟩ := h
  cases lowered : Backend.Stock.lower (function config) with
  | error message => simp [lowered] at h
  | ok result =>
    have both : Backend.Stock.Scalar.check (function config) result.code = true ∧
        aluRootsCovered result = true := by simpa only [lowered,Bool.and_eq_true] using h
    refine ⟨result,rfl,?_⟩
    intro id member
    exact List.contains_iff_mem.mp (List.all_eq_true.mp both.2 id member)
end E2E.StockAluRootsWitness

namespace E2E.StockAluRootsWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0

/-- The actual artifacts inhabit the shared production consumer, rather than a separate
experimental checker or a caller-provided proof contract. -/
theorem compiled_semantic_exists (config : Configuration) (cleanup : Bool) :
    ∃ (result : Stock.Result), ∃ vcp rf af fa fb,
      CompiledSemanticNI (function config) 0 result.code vcp rf af fa fb ∧
      CompiledStockArithmeticStage (function config) cleanup 0 result vcp rf af fa fb ∧
      FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  obtain ⟨domain,result,vcp,rf,af,fa,fb,stage,reads,allocated,covered,legacy⟩ :=
    compiled_exists config cleanup
  exact ⟨result,vcp,rf,af,fa,fb,.scalar domain rfl reads stage,stage,covered⟩

/-- Reusable original syntax for subsequent scalar-family extensions. -/
theorem source_family (config : Configuration) :
    ∀ stm ∈ (function config).blocks[0]!.body, Stock.Proof.HighMulBody.Family stm.inst := family config
end E2E.StockAluRootsWitness
