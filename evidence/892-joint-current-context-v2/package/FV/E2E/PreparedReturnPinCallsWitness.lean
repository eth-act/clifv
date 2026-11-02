import FV.E2E.PreparedReturnPinCalls
import FV.E2E.PreparedReturnPinCallerBoundaryWitness

namespace E2E.PreparedReturnPinCallsWitness
open Backend Backend.Proof Backend.Proof.Driver LinkCheck
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Keep both original inputs, including the complete captured settings and signatures. -/
def input : LinkInput := PreparedReturnPinCallerBoundaryWitness.input

def outputs (cleanup : Bool) : Res := input.resultsProductionWith Stock.VoidCall.NI.lowerValidated cleanup

private def actualStock (cleanup : Bool) (g : Clif.Function) : Bool := match Stock.lower g with
  | .error _ => false
  | .ok result => decide ((artOf (outputs cleanup) g).vc = result.code)

private def checks (cleanup : Bool) : Bool :=
  okRReturnPinCalls (productionStage cleanup) input (outputs cleanup) &&
  (progOf (outputs cleanup)).funcs.all (fun g => !hasTls g) &&
  (progOf (outputs cleanup)).funcs.all (actualStock cleanup) &&
  Stock.VoidCall.NI.check input.funcs[1]!.func (artOf (outputs cleanup) input.funcs[1]!.func).vc &&
  !SemanticNI.check input.funcs[1]!.func (artOf (outputs cleanup) input.funcs[1]!.func).vc

attribute [local irreducible] checks
-- witness: native_decide (the two complete original mixed programs only)
private theorem checks_true : (checks false && checks true) = true := by native_decide

private theorem checked (cleanup : Bool) :
    okRReturnPinCalls (productionStage cleanup) input (outputs cleanup) = true ∧
      (progOf (outputs cleanup)).funcs.all (fun g => !hasTls g) = true := by
  have both := Bool.and_eq_true_iff.mp checks_true
  have h : checks cleanup = true := by
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simp only [checks,Bool.and_eq_true,and_assoc] at h
  exact ⟨h.1,h.2.1⟩

def world (cleanup : Bool) : BitVec 64 → Prop :=
  (ofRes input (outputs cleanup) closedBase (fun _ => False)).Img

def system (cleanup : Bool) : LinkSys := ofRes input (outputs cleanup) closedBase (world cleanup)

private theorem base_ok (cleanup : Bool) : BaseOk (system cleanup) :=
  baseOk_closedR fun g member => by
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp (checked cleanup).2 g member

/-- Both unchanged functions retain their actual raw Stock artifacts in both cleanup modes. -/
theorem original_stock_artifacts (cleanup : Bool) :
    ∀ g ∈ (progOf (outputs cleanup)).funcs,
      ∃ result,Stock.lower g = .ok result ∧ (artOf (outputs cleanup) g).vc = result.code := by
  have both := Bool.and_eq_true_iff.mp checks_true
  have h : checks cleanup = true := by
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simp only [checks,Bool.and_eq_true,and_assoc] at h
  intro g member
  have raw := List.all_eq_true.mp h.2.2.1 g member
  unfold actualStock at raw
  cases lowered : Stock.lower g with
  | error message => simp only [lowered,Bool.false_eq_true] at raw
  | ok result =>
    simp only [lowered,decide_eq_true_eq] at raw
    exact ⟨result,rfl,raw⟩

/-- The complete existing program contract is jointly inhabited by the original caller and sret callee. -/
theorem system_ok (cleanup : Bool) : (system cleanup).OkSemanticReturnPins :=
  semanticPreparedReturnPinCallsResults_sound (productionStage cleanup) (productionStage_cases cleanup)
    (input.resultsProductionWith_prepared Stock.VoidCall.NI.lowerValidated cleanup)
    (checked cleanup).1 (base_ok cleanup) (fun _ h => h)

/-- The original program statement holds for every valid original base and world. -/
theorem program_correct (cleanup : Bool) : CrateStmtReturnPins input (outputs cleanup) input.funcs[1]!.func.name :=
  preparedReturnPinCalls_correct (productionStage cleanup) (productionStage_cases cleanup)
    (input.resultsProductionWith_prepared Stock.VoidCall.NI.lowerValidated cleanup) (checked cleanup).1 _

/-- The transactional producer keeps the complete successful Stock attempt. -/
theorem producer_retains_attempt (cleanup : Bool) : input.resultsReturnPinCalls cleanup = outputs cleanup :=
  input.resultsReturnPinCalls_accept cleanup (checked cleanup).1

/-- Additional negative fixture. Its caller has a nop outside this first call class. -/
def rejectedInput : LinkInput := {input with
  funcs := [input.funcs[0]!,{input.funcs[1]! with
    clif := input.funcs[1]!.clif.replace "%sret_caller" "%sret_caller_with_nop" |>.replace
      "    call fn0" "    nop\n    call fn0"}]
  addrs := input.addrs.map fun pair =>
    if pair.1 = "sret_caller" then ("sret_caller_with_nop",pair.2) else pair}

private def retryChecks (cleanup : Bool) : Bool :=
  !okRReturnPinCalls (productionStage cleanup) rejectedInput
    (rejectedInput.resultsProductionWith Stock.VoidCall.NI.lowerValidated cleanup) &&
  !okRReturnPins (productionStage cleanup) rejectedInput
    (rejectedInput.resultsProductionWith Stock.MemorySretCopy.lowerValidated cleanup) &&
  okRSemanticNI (productionStage cleanup) rejectedInput (rejectedInput.resultsProduction cleanup)

attribute [local irreducible] retryChecks
-- witness: native_decide (the additional two-function negative fixture in both cleanup modes)
private theorem retryChecks_true : (retryChecks false && retryChecks true) = true := by native_decide

private theorem rejected_checks (cleanup : Bool) :
    okRReturnPinCalls (productionStage cleanup) rejectedInput
      (rejectedInput.resultsProductionWith Stock.VoidCall.NI.lowerValidated cleanup) = false ∧
    okRReturnPins (productionStage cleanup) rejectedInput
      (rejectedInput.resultsProductionWith Stock.MemorySretCopy.lowerValidated cleanup) = false ∧
    okRSemanticNI (productionStage cleanup) rejectedInput (rejectedInput.resultsProduction cleanup) = true := by
  have both := Bool.and_eq_true_iff.mp retryChecks_true
  have h : retryChecks cleanup = true := by
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simpa only [retryChecks,Bool.and_eq_true,Bool.not_eq_true',and_assoc] using h

/-- A rejected attempt restores both complete previous artifacts, not only the callee. -/
theorem rejected_program_retried (cleanup : Bool) :
    rejectedInput.resultsReturnPinCalls cleanup = rejectedInput.resultsProduction cleanup := by
  rw [rejectedInput.resultsReturnPinCalls_retry cleanup (rejected_checks cleanup).1,
    rejectedInput.resultsReturnPins_retry cleanup (rejected_checks cleanup).2.1]

/-- The rejected source class keeps the original program's accepted result. -/
theorem rejected_program_accepted (cleanup : Bool) :
    okRReturnPinCalls (productionStage cleanup) rejectedInput (rejectedInput.resultsReturnPinCalls cleanup) = true :=
  rejectedInput.resultsReturnPinCalls_checked cleanup (rejected_checks cleanup).2.2

end E2E.PreparedReturnPinCallsWitness
