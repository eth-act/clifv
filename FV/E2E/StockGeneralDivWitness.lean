import FV.Backend.Proof.RegallocOperands
import FV.E2E.RegLevelPush
import FV.E2E.CompiledSemanticNI
import FV.E2E.StockGeneralDivChecks
namespace E2E.StockGeneralDivNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual source returns/traps inhabit the universal domain and all live
prefix families. These are fixed witness inputs; the source domain is arbitrary. -/
theorem source_cases (config : Configuration) (op : Clif.DivOp) (safe positive : Bool) (layout : Layout) :
    match caseWanted config op safe positive layout with
    | .error code => caseRun config op safe positive layout = .trapped code
    | .ok bits => ∃ mem,caseRun config op safe positive layout = .returned [⟨valueType config,bits⟩] mem := by
  have h := List.all_eq_true.mp checks_true config (by cases config <;> simp [configurations])
  have h := List.all_eq_true.mp h op (by cases op <;> simp [operations,StockDivNIWitness.operations])
  have h := List.all_eq_true.mp h safe (by cases safe <;> simp)
  have h := List.all_eq_true.mp h layout (by cases layout <;> simp [layouts])
  simp only [Bool.and_eq_true] at h
  have casesOk := h.1.1
  simp only [sourceCases,Bool.and_eq_true] at casesOk
  have checked : outcomeAgrees (valueType config) (caseWanted config op safe positive layout)
      (caseRun config op safe positive layout) = true := by
    cases positive with
    | false => exact casesOk.1
    | true => exact casesOk.2
  have result := outcomeAgrees_sound (ty := valueType config)
    (wanted := caseWanted config op safe positive layout) (actual := caseRun config op safe positive layout) checked
  cases wanted : caseWanted config op safe positive layout <;> simpa only [wanted] using result

/-- Actual checked/allocated/emitted artifacts inhabit the complete division
semantic domain in every ABI and cleanup mode, beyond the legacy checker. -/
theorem compiled_exists (config : Configuration) (op : Clif.DivOp) (safe : Bool) (layout : Layout) (cleanup : Bool) :
    Stock.Scalar.Domain (function config op safe layout) ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage (function config op safe layout) cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI (function config op safe layout) 0 result.code vcp rf af fa fb ∧
      Stock.Scalar.lowerValidated (function config op safe layout) = .ok result.code ∧
      DivBoundary.check (function config op safe layout).sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  have h : checks config op safe layout cleanup = true := by
    have both := List.all_eq_true.mp checks_true config (by cases config <;> simp [configurations])
    have both := List.all_eq_true.mp both op (by cases op <;> simp [operations,StockDivNIWitness.operations])
    have both := List.all_eq_true.mp both safe (by cases safe <;> simp)
    have both := List.all_eq_true.mp both layout (by cases layout <;> simp [layouts])
    simp only [Bool.and_eq_true] at both
    cases cleanup with
    | false => exact both.1.2
    | true => exact both.2
  simp only [checks,Bool.and_eq_true] at h
  obtain ⟨⟨⟨scope,dominated⟩,abi⟩,h⟩ := h
  have supported : (body config op safe layout).all Stock.Scalar.generalDivBodyEligible = true := by
    cases config <;> cases safe <;> cases layout <;> rfl
  have family : ∀ stm ∈ (function config op safe layout).blocks[0]!.body,
      Stock.Proof.HighMulBody.Family stm.inst ∨ ∃ op ty x y,stm.inst = .div op ty x y := by
    intro stm member
    have member' : stm ∈ body config op safe layout := by
      cases config <;> cases safe <;> cases layout <;> exact member
    exact Stock.Scalar.generalDivBodyEligible_sound (List.all_eq_true.mp supported stm member')
  have domain : Stock.Scalar.Domain (function config op safe layout) :=
    Stock.Scalar.domain_of_scalar_div (lowerScope_of scope) (dominated_of dominated) abi
      (b := (function config op safe layout).blocks[0]!)
      (by cases config <;> cases safe <;> cases layout <;> rfl) family
      (xs := [returned layout]) (by cases config <;> cases safe <;> cases layout <;> rfl)
      (by cases config <;> rfl)
  refine ⟨domain,?_⟩
  cases lowered : Stock.lower (function config op safe layout) with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨reads,scalar⟩,paired⟩,actual⟩,h⟩ := h
    have actualLower : Stock.Scalar.lowerValidated (function config op safe layout) = .ok result.code := by
      cases observed : Stock.Scalar.lowerValidated (function config op safe layout) with
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
            cases emittedLayout : fa.layout with
            | error message => rw [emittedLayout] at layoutOk; change false = true at layoutOk; cases layoutOk
            | ok fb =>
              have check : checkAlloc vcp rf = .ok () := by
                cases check : checkAlloc vcp rf with
                | error message => rw [check] at checked; change false = true at checked; cases checked
                | ok value => cases value; rfl
              have stage : CompiledStockArithmeticStage (function config op safe layout) cleanup 0 result vcp rf af fa fb :=
                ⟨lowered,prepared,prepOk,check,physical,emitted,emittedLayout⟩
              exact ⟨result,vcp,rf,af,fa,fb,stage,.scalarDiv domain rfl reads stage,
                actualLower,reads,allocated,(formsCoveredB_iff _ _).mp covered⟩

/-- Complete entry retains arbitrary source values and explicit slot address. -/
theorem source_entry (config : Configuration) (op : Clif.DivOp) (safe : Bool) (layout : Layout)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    ClifEntry (function config op safe layout) (arguments config input)
      ⟨frame config op safe layout input slot,[],Clif.Mem.empty⟩ := by
  cases config <;> cases safe <;> cases layout <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

end E2E.StockGeneralDivNIWitness
