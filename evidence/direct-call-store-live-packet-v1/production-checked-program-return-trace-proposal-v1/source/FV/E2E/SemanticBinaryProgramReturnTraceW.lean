import FV.E2E.SemanticBinaryReturnTraceW
import FV.E2E.LinkReturnPinGoodWInternal

namespace E2E.SemanticBinary
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Checked artifacts supply the linked return driver for every depth. -/
theorem linked_return_traceW_of_checked_input
    {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    {modes : Clif.Function → ReturnPinMode} {κ : Nat → Clif.Function → Nat}
    (checked : (SemanticStackBound.ofInput I B F).OkReturnPins modes)
    [(SemanticStackBound.ofInput I B F).CrunOk]
    (budget : (SemanticStackBound.ofInput I B F).Budget κ) :
    ∀ depth, (SemanticStackBound.ofInput I B F).ThmGW κ depth :=
  (SemanticStackBound.ofInput I B F).thmGW_return_pins_internal checked budget

/-- The linked driver and image facts use one checked result table. -/
theorem linked_return_traceW_and_imageFacts
    {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    {modes : Clif.Function → ReturnPinMode} {κ : Nat → Clif.Function → Nat}
    (checked : (SemanticStackBound.ofInput I B F).OkReturnPins modes)
    [(SemanticStackBound.ofInput I B F).CrunOk]
    (budget : (SemanticStackBound.ofInput I B F).Budget κ) :
    (∀ depth, (SemanticStackBound.ofInput I B F).ThmGW κ depth) ∧
      BinaryBoundaryFacts.Facts I :=
  ⟨linked_return_traceW_of_checked_input checked budget,
    BinaryBoundaryFacts.of_returnPins checked⟩

end E2E.SemanticBinary
