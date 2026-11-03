import FV.E2E.CompiledSemanticReturnPins
import FV.E2E.StockMemorySretCopyCompiledWitness

namespace E2E.CompiledSemanticReturnPinsWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.StoreRoots.ComputedFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def rejectsPrevious : Bool :=
  match Stock.lower function with
  | .error _ => false
  | .ok result => !SemanticNI.check function result.code

private theorem rejectsPrevious_true : rejectsPrevious = true := by native_decide

/-- The unchanged sret capture derives the new mode from actual checks in both cleanup modes. -/
theorem checked_sret_pins_witness (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc) (frame : AFunc)
      (assembly : FnAsm) (binary : FnBin),
      Stock.lower function = .ok result ∧
      Stock.MemorySretCopy.lowerValidated function = .ok result.code ∧
      ReturnPinMode.checked function result.code = .stockABI ∧
      CompiledSemanticReturnPins function 0 result.code prepared allocated frame assembly binary
        (ReturnPinMode.checked function result.code) ∧
      CompiledSemanticABI function 0 result.code prepared allocated frame assembly binary ∧
      FormsCovered ⟨assembly.k,frame.slotBase⟩ prepared := by
  obtain ⟨result,prepared,allocated,frame,assembly,binary,lowered,provider,source,stage,covered⟩ :=
    StockMemorySretCopyCompiledWitness.compiled_sret_stage_witness cleanup
  have rejected := rejectsPrevious_true
  unfold rejectsPrevious at rejected
  rw [lowered] at rejected
  have old : SemanticNI.check function result.code = false := by
    simpa only [Bool.not_eq_true'] using rejected
  have mode : ReturnPinMode.checked function result.code = .stockABI := by
    simp only [ReturnPinMode.checked,old,Bool.false_eq_true,↓reduceIte]
  have artifact : CompiledSemanticReturnPins function 0 result.code prepared allocated frame assembly binary
      (ReturnPinMode.checked function result.code) :=
    CompiledSemanticReturnPins.of_checks (by simp only [SemanticABI.check,source,Bool.or_true])
      stage.prepare stage.prepOk stage.check stage.alloc stage.emit stage.layout
  exact ⟨result,prepared,allocated,frame,assembly,binary,lowered,provider,mode,artifact,artifact.erase,covered⟩

/-- The original source selects x8. The retained ordinary mode still selects x0. -/
theorem physical_pin_witness :
    ReturnPinMode.stockABI.Valid function [(.vreg 9 .int,.x 8)] ∧
      ReturnPinMode.stockABI.pins function 1 = [.x 8] ∧
      ReturnPinMode.ordinary.pins function 1 = [.x 0] := by
  unfold ReturnPinMode.Valid ReturnPinMode.pins ReturnABI
  native_decide

end E2E.CompiledSemanticReturnPinsWitness
