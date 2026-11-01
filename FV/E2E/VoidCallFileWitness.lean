import FV.E2E.VoidCallFilePipeline
import FV.E2E.PreparedReturnPinCallsWitness
import FV.Backend.LinearScan

namespace E2E.VoidCallFileWitness.File
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
open Backend E2E.LinkCheck

def checks (cleanup : Bool) : Bool :=
  let input := E2E.PreparedReturnPinCallsWitness.input
  match input.funcs.mapM (fun fi => ReturnPinFile.entry fi.func true cleanup) with
  | .error _ => false
  | .ok entries => ReturnPinFile.check entries && entries.all fun e =>
      SemanticABI.checkCalls e.source e.raw &&
      match Stock.lower e.source with
      | .error _ => false
      | .ok result => decide (e.raw = result.code)

-- witness: native_decide (the unchanged mixed program in both cleanup modes only)
theorem mixed_entry_checks : (checks false && checks true) = true := by native_decide

def parsed (I : LinkInput) : Clif.ParsedFile := Clif.parseFile (String.join (I.funcs.map (·.clif)))

def fileChecks (cleanup : Bool) : Bool :=
  let pf := parsed E2E.PreparedReturnPinCallsWitness.input
  let result := Id.run (compileFileVoidCallABIWhen true (fun vcs => pure (allocateLean vcs)) pf [] cleanup)
  let attempt := Id.run (compileFileWithLowering lowerForAllocationVoidCallABI VCode.rulesFired
    (fun vcs => pure (allocateLean vcs)) pf [] cleanup)
  let original := Id.run (compileFileMemoryCapturedCopyNIWhen true
    (fun vcs => pure (allocateLean vcs)) pf [] cleanup)
  let rejected := parsed E2E.PreparedReturnPinCallsWitness.rejectedInput
  let retry := Id.run (compileFileVoidCallABIWhen true (fun vcs => pure (allocateLean vcs)) rejected [] cleanup)
  let previous := Id.run (compileFileMemoryCapturedCopyNIWhen true
    (fun vcs => pure (allocateLean vcs)) rejected [] cleanup)
  decide (result.funcs.length = 2) && result.unsupported.isEmpty && result.unverified.isEmpty &&
    result.unvalidated.isEmpty && decide (result.object = attempt.object) &&
    decide (result.object ≠ original.object) &&
    decide ((pf.funcs.filterMap (·.func.toOption)) =
      E2E.PreparedReturnPinCallsWitness.input.funcs.map FnInput.func) &&
    !(ReturnPinFile.entries rejected [] cleanup).toOption.any ReturnPinFile.check &&
    decide (retry.object = previous.object) &&
    previous.unsupported.isEmpty && previous.unverified.isEmpty

-- witness: native_decide (the fixed complete files in both cleanup modes only)
theorem mixed_file_checks : (fileChecks false && fileChecks true) = true := by native_decide

def allocationRetry (cleanup : Bool) : Bool :=
  let pf := parsed E2E.PreparedReturnPinCallsWitness.input
  let failed : StateM Nat FileAsm := compileFileVoidCallABIWhen true (fun vcs => do
    let count ← get
    set (count+1)
    pure (if count == 0 then vcs.map (fun _ => .error "forced complete attempt failure")
      else allocateLean vcs)) pf [] cleanup
  let (output,count) := failed.run 0
  let previous := Id.run (compileFileMemoryCapturedCopyNIWhen true
    (fun vcs => pure (allocateLean vcs)) pf [] cleanup)
  decide (2 ≤ count) && decide (output.object = previous.object) && previous.unsupported.isEmpty

-- witness: native_decide (fixed callback failure in both cleanup modes only)
theorem complete_allocation_retry : (allocationRetry false && allocationRetry true) = true := by native_decide

end E2E.VoidCallFileWitness.File

namespace E2E.VoidCallFileWitness.Program
open Backend Backend.Proof Backend.Proof.Driver E2E E2E.LinkCheck
open E2E.LinkCheck.VoidCallFile
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

abbrev input := E2E.PreparedReturnPinCallsWitness.input

def outputs (cleanup : Bool) : Res :=
  input.resultsWithLowering (fun f => lowerCheckedVoidCallABI f true) (productionStage cleanup)

def checks (cleanup : Bool) : Bool :=
  okRSemanticFor returnPinCallsExtra (productionStage cleanup) input (outputs cleanup) &&
  ((progOf (outputs cleanup)).funcs.mapM (fun g => ReturnPinFile.entry g true cleanup)).toOption.any
    ReturnPinFile.check &&
  (progOf (outputs cleanup)).funcs.all (fun g => !hasTls g) &&
  (progOf (outputs cleanup)).funcs.all (fun g => match Stock.lower g with
    | .error _ => false
    | .ok result => decide ((artOf (outputs cleanup) g).vc = result.code))

-- witness: native_decide (the two original complete mixed program instances only)
theorem checks_true : (checks false && checks true) = true := by native_decide

theorem checked (cleanup : Bool) :
    okRSemanticFor returnPinCallsExtra (productionStage cleanup) input (outputs cleanup) = true ∧
    ((progOf (outputs cleanup)).funcs.mapM (fun g => ReturnPinFile.entry g true cleanup)).toOption.any
      ReturnPinFile.check = true ∧
    (progOf (outputs cleanup)).funcs.all (fun g => !hasTls g) = true := by
  have both := Bool.and_eq_true_iff.mp checks_true
  have row : checks cleanup = true := by cases cleanup <;> first | exact both.1 | exact both.2
  simp only [checks,Bool.and_eq_true,and_assoc] at row
  exact ⟨row.1,row.2.1,row.2.2.1⟩

def world (cleanup : Bool) : BitVec 64 → Prop :=
  (ofRes input (outputs cleanup) closedBase (fun _ => False)).Img

def system (cleanup : Bool) : LinkSys := ofRes input (outputs cleanup) closedBase (world cleanup)

theorem base_ok (cleanup : Bool) : BaseOk (system cleanup) :=
  baseOk_closedR fun g member => by
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp (checked cleanup).2.2 g member

/-- The original mixed source jointly inhabits the complete program contract. -/
theorem system_ok (cleanup : Bool) : (system cleanup).OkSemanticReturnPins :=
  results_sound input cleanup (fun _ => true) (checked cleanup).1 (checked cleanup).2.1
    (base_ok cleanup) (fun _ h => h)

theorem program_correct (cleanup : Bool) (name : String) :
    CrateStmtReturnPins input (outputs cleanup) name :=
  results_correct input cleanup (fun _ => true) (checked cleanup).1 (checked cleanup).2.1 name

end E2E.VoidCallFileWitness.Program
