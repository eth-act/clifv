import FV.E2E.StockNotFixtures
import FV.E2E.StockScalarNI
import FV.E2E.CompiledSemanticNI
import FV.Backend.LinearScan
import FV.Backend.Lowering.StockD0

namespace E2E.StockNotNIWitness
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
end E2E.StockNotNIWitness



namespace E2E.StockNotNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0

private theorem family (config : Configuration) :
    ∀ stm ∈ (function config).blocks[0]!.body, Stock.Proof.BnotBody.Family stm.inst := by
  intro stm member
  let ty := valueType config
  change stm ∈ [⟨[9],.iconst ty (BitVec.ofNat ty.width 0x123456789abcdef)⟩,
    ⟨[10],.iconst ty (BitVec.ofNat ty.width 4097)⟩,
    ⟨[11],.binary .iadd ty 1 9⟩,⟨[12],.binary .band ty 11 8⟩,
    ⟨[13],.binary .bxor ty 12 2⟩,⟨[14],.binary .bor ty 13 9⟩,
    ⟨[15],.select ty 0 14 12⟩,⟨[16],.binary .isub ty 15 2⟩,
    ⟨[17],.binary .iadd ty 16 10⟩,⟨[18],.iconst ty (BitVec.ofNat ty.width 42)⟩,
    ⟨[19],.binary .band ty 1 8⟩,
    ⟨[20],.unary .bnot ty 17⟩,⟨[21],.binary .bxor ty 20 2⟩,
    ⟨[22],.unary .bnot ty 21⟩,⟨[23],.binary .iadd ty 22 10⟩,
    ⟨[24],.binary .band ty 23 8⟩,⟨[25],.unary .bnot ty 24⟩,
    ⟨[26],.unary .bnot ty 1⟩] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact .inl (.inr ⟨ty,_,rfl⟩)
  · exact .inl (.inr ⟨ty,_,rfl⟩)
  · exact .inl (.inl (.inl ⟨false,ty,1,9,rfl⟩))
  · exact .inl (.inl (.inr (.inr ⟨.band,ty,11,8,rfl⟩)))
  · exact .inl (.inl (.inr (.inr ⟨.bxor,ty,12,2,rfl⟩)))
  · exact .inl (.inl (.inr (.inr ⟨.bor,ty,13,9,rfl⟩)))
  · exact .inl (.inl (.inr (.inl ⟨ty,0,14,12,rfl⟩)))
  · exact .inl (.inl (.inl ⟨true,ty,15,2,rfl⟩))
  · exact .inl (.inl (.inl ⟨false,ty,16,10,rfl⟩))
  · exact .inl (.inr ⟨ty,_,rfl⟩)
  · exact .inl (.inl (.inr (.inr ⟨.band,ty,1,8,rfl⟩)))

  · exact .inr ⟨ty,17,rfl⟩
  · exact .inl (.inl (.inr (.inr ⟨.bxor,ty,20,2,rfl⟩)))
  · exact .inr ⟨ty,21,rfl⟩
  · exact .inl (.inl (.inl ⟨false,ty,22,10,rfl⟩))
  · exact .inl (.inl (.inr (.inr ⟨.band,ty,23,8,rfl⟩)))
  · exact .inr ⟨ty,24,rfl⟩
  · exact .inr ⟨ty,1,rfl⟩

/-- Reuse the fixed original source family when extending complete witnesses. -/
theorem source_family (config : Configuration) :
    ∀ stm ∈ (function config).blocks[0]!.body, Stock.Proof.BnotBody.Family stm.inst := family config

/-- Actual checked/allocated/emitted artifacts inhabit the complete mixed
semantic domain in every ABI and cleanup mode, beyond the legacy checker. -/
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
    Stock.Scalar.domain_of_bnot (lowerScope_of scope) (dominated_of dominated) abi
      (b := (function config).blocks[0]!) rfl (family config) (xs := [25]) rfl (by rfl)
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

def arguments (config : Configuration) (input : Nat → BitVec (valueType config).width) : List Clif.Val :=
  (List.range 9).map fun i => ⟨valueType config,input i⟩

def frame (config : Configuration) (input : Nat → BitVec (valueType config).width) (slot : Nat) : Clif.Frame := {
  func := function config
  regs := (Clif.Regs.empty.setMany (List.range 9) (arguments config input)).getD Clif.Regs.empty
  slots := [(7,slot)]
  body := (function config).blocks[0]!.body
  term := .ret [25] }

/-- All entry values and the original explicit-slot address remain arbitrary. -/
theorem source_entry (config : Configuration) (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    ClifEntry (function config) (arguments config input) ⟨frame config input slot,[],Clif.Mem.empty⟩ := by
  cases config <;> exact ⟨rfl,rfl,rfl,⟨_,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

/-- Full reference execution includes dependent selection, the consumed stack
argument and the dead statement, for arbitrary values in all six configurations. -/
theorem source_returns (config : Configuration) (input : Nat → BitVec (valueType config).width) (slot : Nat) :
    Clif.runLoop Clif.Env.empty {funcs := []} 19 ⟨frame config input slot,[],Clif.Mem.empty⟩ =
.returned [⟨valueType config,resultValue config input⟩] Clif.Mem.empty := by
  cases config <;> rfl
end E2E.StockNotNIWitness

namespace E2E.StockNotNIWitness
private def classChecks (config : Backend.Stock.D0.Configuration) : Bool :=
  Backend.Stock.Scalar.sourceOk (function config) &&
  match Backend.Stock.lower (function config) with
  | .error _ => false
  | .ok result => Backend.Stock.Scalar.check (function config) result.code

-- witness: native_decide (six fixed actual source/provenance checks only)
theorem source_checks_true : Backend.Stock.D0.configurations.all classChecks = true := by native_decide

/-- Actual source inputs and outputs jointly inhabit both new executable
checks in every ABI, including the guarded empty-edge property. -/
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
  | ok result => exact ⟨result,rfl,source,by simpa only [lowered] using h⟩
end E2E.StockNotNIWitness

namespace E2E.StockNotNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0

/-- The actual mixed artifacts inhabit the shared production consumer, rather
than a separate experimental checker or a caller-provided proof contract. -/
theorem compiled_semantic_exists (config : Configuration) (cleanup : Bool) :
    ∃ (result : Stock.Result), ∃ vcp rf af fa fb,
      CompiledSemanticNI (function config) 0 result.code vcp rf af fa fb ∧
      CompiledStockArithmeticStage (function config) cleanup 0 result vcp rf af fa fb ∧
      FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  obtain ⟨domain,result,vcp,rf,af,fa,fb,stage,reads,allocated,covered,legacy⟩ :=
    compiled_exists config cleanup
  exact ⟨result,vcp,rf,af,fa,fb,.scalar domain rfl reads stage,stage,covered⟩

end E2E.StockNotNIWitness
