import FV.E2E.StockHighMulWitness
import FV.E2E.StockMixedDivChecks
namespace E2E.StockMixedDivNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Actual source returns/traps inhabit the universal domain and all live
prefix families. These are fixed witness inputs; the source domain is arbitrary. -/
theorem source_cases (config : Configuration) (op : Clif.DivOp) (safe positive : Bool) :
    match caseWanted config op safe positive with
    | .error code => caseRun config op safe positive = .trapped code
    | .ok bits => ∃ mem,caseRun config op safe positive = .returned [⟨valueType config,bits⟩] mem := by
  have h := List.all_eq_true.mp checks_true config (by cases config <;> simp [configurations])
  have h := List.all_eq_true.mp h op (by cases op <;> simp [operations,StockDivNIWitness.operations])
  have h := List.all_eq_true.mp h safe (by cases safe <;> simp)
  simp only [Bool.and_eq_true] at h
  have casesOk := h.1.1
  simp only [sourceCases,Bool.and_eq_true] at casesOk
  have checked : outcomeAgrees (valueType config) (caseWanted config op safe positive)
      (caseRun config op safe positive) = true := by
    cases positive with
    | false => exact casesOk.1
    | true => exact casesOk.2
  have result := outcomeAgrees_sound (ty := valueType config)
    (wanted := caseWanted config op safe positive) (actual := caseRun config op safe positive) checked
  cases wanted : caseWanted config op safe positive <;> simpa only [wanted] using result

/-- Actual checked/allocated/emitted artifacts inhabit the complete division
semantic domain in every ABI and cleanup mode, beyond the legacy checker. -/
theorem compiled_exists (config : Configuration) (op : Clif.DivOp) (safe : Bool) (cleanup : Bool) :
    Stock.Scalar.Domain (function config op safe) ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage (function config op safe) cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI (function config op safe) 0 result.code vcp rf af fa fb ∧
      Stock.Scalar.lowerValidated (function config op safe) = .ok result.code ∧
      DivBoundary.check (function config op safe).sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp ∧
      lowerCheck (function config op safe) result.code = false := by
  have h : checks config op safe cleanup = true := by
    have both := List.all_eq_true.mp checks_true config (by cases config <;> simp [configurations])
    have both := List.all_eq_true.mp both op (by cases op <;> simp [operations,StockDivNIWitness.operations])
    have both := List.all_eq_true.mp both safe (by cases safe <;> simp)
    simp only [Bool.and_eq_true] at both
    cases cleanup with
    | false => exact both.1.2
    | true => exact both.2
  simp only [checks,Bool.and_eq_true] at h
  obtain ⟨⟨⟨scope,dominated⟩,abi⟩,h⟩ := h
  have family : ∀ item ∈ frontBody config safe, Stock.Proof.HighMulBody.Family item.inst := by
    intro item member
    rcases List.mem_append.mp member with old | extra
    · exact StockHighMulNIWitness.source_family config item old
    · cases safe
      · simp [frontBody] at extra
      · simp only [if_true,List.mem_singleton] at extra
        subst item
        exact Stock.Scalar.highmulBodyEligible_sound (by cases config <;> rfl)
  have domain : Stock.Scalar.Domain (function config op safe) :=
    Stock.Scalar.domain_of_mixed_div (lowerScope_of scope) (dominated_of dominated) abi
      (b := (function config op safe).blocks[0]!) (by cases config <;> cases safe <;> rfl)
      (front := frontBody config safe) (stm := ⟨[5000],.div op (valueType config) 4008 (divisor safe)⟩)
      (by cases config <;> cases safe <;> rfl) family rfl rfl
      (by cases config <;> cases safe <;> rfl) (by cases config <;> rfl)
  refine ⟨domain,?_⟩
  cases lowered : Stock.lower (function config op safe) with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨legacy,reads⟩,scalar⟩,paired⟩,actual⟩,h⟩ := h
    have actualLower : Stock.Scalar.lowerValidated (function config op safe) = .ok result.code := by
      cases observed : Stock.Scalar.lowerValidated (function config op safe) with
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
              have stage : CompiledStockArithmeticStage (function config op safe) cleanup 0 result vcp rf af fa fb :=
                ⟨lowered,prepared,prepOk,check,physical,emitted,layout⟩
              exact ⟨result,vcp,rf,af,fa,fb,stage,.scalarDiv domain rfl reads stage,
                actualLower,reads,allocated,(formsCoveredB_iff _ _).mp covered,legacy⟩

/-- Complete entry retains arbitrary source values and explicit slot address. -/
theorem source_entry (config : Configuration) (op : Clif.DivOp) (safe : Bool)
    (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    ClifEntry (function config op safe) (arguments config input)
      ⟨frame config op safe input slot,[],Clif.Mem.empty⟩ := by
  cases config <;> cases safe <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

end E2E.StockMixedDivNIWitness
