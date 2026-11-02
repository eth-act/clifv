import FV.E2E.ReturnPinGeneratedStackKernel
import FV.E2E.ReturnPinBinary

namespace E2E.ReturnPinGeneratedStack
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

/-- Keep the original stack statement while using the complete ABI-aware program contract. -/
theorem crate_correct_stackN {I : SemanticStackBound.CompilerInput}
    (checked : ReturnPinBinary.okB I = true) {name : String}
    (good : SemanticStackBound.goodN I name = true) : SemanticStackBound.StackStmt I name := by
  apply E2E.ReturnPinGeneratedStackFor.crate_correct_stackN (admission := E2E.LinkCheck.ReturnPinAdmission.previous) <;> assumption

/-- Preserve the original all-entry stack variant and its computed bound. -/
theorem crate_correct_stack {I : SemanticStackBound.CompilerInput}
    (checked : ReturnPinBinary.okB I = true) {S : Nat}
    (bound : SemanticStackBound.stackB I = some S) (name : String) : SemanticStackBound.StackStmt I name := by
  apply E2E.ReturnPinGeneratedStackFor.crate_correct_stack (admission := E2E.LinkCheck.ReturnPinAdmission.previous) <;> assumption

end E2E.ReturnPinGeneratedStack
