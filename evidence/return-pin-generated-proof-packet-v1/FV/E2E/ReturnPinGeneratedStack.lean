import FV.E2E.ReturnPinBinary

namespace E2E.ReturnPinGeneratedStack
open Backend Backend.Proof Backend.Proof.Driver E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false

/-- Keep the original stack statement while using the complete ABI-aware program contract. -/
theorem crate_correct_stackN {I : SemanticStackBound.CompilerInput}
    (checked : ReturnPinBinary.okB I = true) {name : String}
    (good : SemanticStackBound.goodN I name = true) : SemanticStackBound.StackStmt I name := by
  intro B F base world f found M ra s initial args cs entry room free frame image body arguments source
    avoids relation placement traps
  exact (ReturnPinStackBound.crate_correct_stackNX checked good B F base world f found M ra s initial
    args cs entry room free frame image body arguments source avoids relation placement traps).1

/-- Preserve the original all-entry stack variant and its computed bound. -/
theorem crate_correct_stack {I : SemanticStackBound.CompilerInput}
    (checked : ReturnPinBinary.okB I = true) {S : Nat}
    (bound : SemanticStackBound.stackB I = some S) (name : String) : SemanticStackBound.StackStmt I name := by
  intro B F base world f found
  have good : SemanticStackBound.goodN I name = true := by
    unfold SemanticStackBound.goodN
    rw [found]
    exact (SemanticStackBound.stackB_some bound).1 f (Clif.Program.func?_some found).1
  exact crate_correct_stackN checked good B F base world f found

end E2E.ReturnPinGeneratedStack
