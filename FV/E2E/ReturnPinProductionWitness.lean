import FV.Backend.ReturnPinProduction
import FV.E2E.PreparedReturnPinCallsWitness
import FV.Backend.LinearScan

namespace E2E.ReturnPinProductionWitness
open Backend E2E.LinkCheck
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

/-- Keep the complete original captured caller and callee. -/
def original : Clif.ParsedFile :=
  Clif.parseFile (String.join (PreparedReturnPinCallsWitness.input.funcs.map (·.clif)))

/-- The unrelated float leaf must retain the previous whole-file mode. -/
def mixed : Clif.ParsedFile := Clif.parseFile
  (String.join (PreparedReturnPinCallsWitness.input.funcs.map (·.clif)) ++
    "\nfunction %float_leaf(f64) -> f64 {\nblock0(v0: f64):\n return v0\n}\n")

private def checks (cleanup : Bool) : Bool :=
  original.funcs.length == 2 && mixed.funcs.length == 3 &&
  mixed.funcs.all (fun p => p.func.isOk) &&
  returnPinModeB original [] cleanup && !returnPinModeB mixed [] cleanup &&
  let alloc := fun (vcs : Array VCode) => Id.run (pure (allocateLean vcs))
  let selected := Id.run (compileFileReturnPinWhen true (fun vcs => pure (alloc vcs)) original [] cleanup)
  let attempt := Id.run (compileFileVoidCallABIWhen true (fun vcs => pure (alloc vcs)) original [] cleanup)
  decide (selected.object = attempt.object) && selected.unsupported.isEmpty && selected.layout.isOk

-- witness: native_decide (the complete captured input and unrelated float leaf only)
private theorem checks_true : (checks false && checks true) = true := by native_decide

private theorem mode_facts (cleanup : Bool) :
    returnPinModeB original [] cleanup = true ∧ returnPinModeB mixed [] cleanup = false := by
  have both := Bool.and_eq_true_iff.mp checks_true
  have h : checks cleanup = true := by
    cases cleanup with
    | false => exact both.1
    | true => exact both.2
  simp only [checks,Bool.and_eq_true,and_assoc,Bool.not_eq_true'] at h
  exact ⟨h.2.2.2.1,h.2.2.2.2.1⟩

/-- Every allocator and its effects remain exact when the float mode rejects ABI admission. -/
theorem mixed_previous_action {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (cleanup : Bool) :
    compileFileReturnPinWhen true alloc mixed [] cleanup =
      compileFileMemoryCapturedCopyNIWhen true alloc mixed [] cleanup :=
  compileFileReturnPinWhen_retry alloc mixed [] cleanup (mode_facts cleanup).2

/-- Both cleanup modes retain the actual new artifacts for the original captured program. -/
theorem original_admitted {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (cleanup : Bool) :
    compileFileReturnPinWhen true alloc original [] cleanup =
      compileFileVoidCallABIWhen true alloc original [] cleanup :=
  compileFileReturnPinWhen_admitted alloc original [] cleanup (mode_facts cleanup).1

end E2E.ReturnPinProductionWitness
