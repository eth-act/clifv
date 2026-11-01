import FV.E2E.StockProductionFixtures
import FV.E2E.CompiledSemanticNI
import FV.Backend.LinearScan
import FV.Backend.Lowering.StockD0

namespace E2E.StockArithmeticNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private def checks (config : Configuration) (cleanup : Bool) : Bool :=
  Stock.Arithmetic.sourceOk (function config) &&
  match Stock.lower (function config) with
  | .error _ => false
  | .ok result =>
    !lowerCheck (function config) result.code && SemanticNI.check (function config) result.code &&
    ABIReadOnly.check (function config).sig result.code &&
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

/-- Fixed compiler-data witness only: all twelve ABI/cleanup combinations
complete the real pipeline, including an actually consumed stack argument. -/
theorem checks_true : grid = true := by native_decide

/-- Actual artifacts jointly inhabit the source, ABI-read, paired consumer,
allocator and emitted/layout contracts beyond the legacy checker domain. -/
theorem compiled_exists (config : Configuration) (cleanup : Bool) :
    Stock.Arithmetic.Domain (function config) ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage (function config) cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI (function config) 0 result.code vcp rf af fa fb ∧
      ABIReadOnly.check (function config).sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp ∧
      lowerCheck (function config) result.code = false := by
  have h : checks config cleanup = true := by
    have both := List.all_eq_true.mp checks_true config
      (by cases config <;> simp [configurations])
    simp only [Bool.and_eq_true] at both
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simp only [checks,Bool.and_eq_true] at h
  obtain ⟨source,h⟩ := h
  refine ⟨Stock.Arithmetic.sourceOk_sound source,?_⟩
  cases lowered : Stock.lower (function config) with
  | error message => simp [lowered] at h
  | ok result =>
    simp only [lowered,Bool.and_eq_true,Bool.not_eq_true'] at h
    obtain ⟨⟨⟨legacy,semantic⟩,reads⟩,h⟩ := h
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
                CompiledSemanticNI.of_checks semantic
                  (by rwa [Stock.Arithmetic.stageF_of_lowerCheck_false legacy])
                  (by rwa [Stock.Arithmetic.stageF_of_lowerCheck_false legacy])
                  check physical emitted layout,
                reads,allocated,(formsCoveredB_iff _ _).mp covered,legacy⟩

/-- Arbitrary entry values, including every unused parameter. -/
def arguments (config : Configuration) (input : Nat → BitVec (valueType config).width) : List Clif.Val :=
  (List.range 9).map fun i => ⟨valueType config,input i⟩

def frame (config : Configuration) (input : Nat → BitVec (valueType config).width) (slot : Nat) : Clif.Frame := {
  func := function config
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments config input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := (function config).blocks[0]!.body
  term := .ret [10] }

/-- The original source entry permits arbitrary values and caller slot
addresses, including the seven values not returned directly. -/
theorem source_entry (config : Configuration) (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    ClifEntry (function config) (arguments config input) ⟨frame config input slot,[],Clif.Mem.empty⟩ := by
  cases config <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

/-- Both arithmetic steps and the return run on arbitrary source values. -/
theorem source_returns (config : Configuration) (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    Clif.runLoop Clif.Env.empty {funcs := []} 3 ⟨frame config input slot,[],Clif.Mem.empty⟩ =
      .returned [⟨valueType config,(input 0 + input 8) - input 1⟩] Clif.Mem.empty := by
  cases config <;> rfl

end E2E.StockArithmeticNIWitness
