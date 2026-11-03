import FV.E2E.CompiledReturnPinReturnTraceW
import FV.E2E.BinaryBoundaryFacts

namespace E2E.SemanticBinary
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The existing checked input supplies the provider for its actual artifact. -/
theorem worldReturnTraceProvider_of_checked_input
    {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    {modes : Clif.Function → ReturnPinMode}
    (checked : (SemanticStackBound.ofInput I B F).OkReturnPins modes)
    {f : Clif.Function} (member : f ∈ (prog I).funcs) :
    WorldReturnTraceProvider (prog I).bare f (art I f).vc (art I f).vcp
      (art I f).rf (art I f).af (art I f).fa (art I f).fb ((modes f).Valid f) := by
  exact worldReturnTraceProvider_artifact (checked.subset f member)
    (checked.compiled f member).artifact

/-- The return provider and image facts use the same checked results. -/
theorem returnTraceProvider_and_imageFacts
    {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    {modes : Clif.Function → ReturnPinMode}
    (checked : (SemanticStackBound.ofInput I B F).OkReturnPins modes)
    {f : Clif.Function} (member : f ∈ (prog I).funcs) :
    WorldReturnTraceProvider (prog I).bare f (art I f).vc (art I f).vcp
      (art I f).rf (art I f).af (art I f).fa (art I f).fb ((modes f).Valid f) ∧
      BinaryBoundaryFacts.Facts I :=
  ⟨worldReturnTraceProvider_of_checked_input checked member,
    BinaryBoundaryFacts.of_returnPins checked⟩

/-- The existing image theorem covers the model of that actual artifact. -/
theorem image_of_checked_codeAddr
    {I : SemanticStackBound.CompilerInput} {B : BaseEnv} {F : BitVec 64 → Prop}
    {modes : Clif.Function → ReturnPinMode}
    (checked : (SemanticStackBound.ofInput I B F).OkReturnPins modes)
    {f : Clif.Function} (member : f ∈ (prog I).funcs)
    {r : Arm.ArmState} {a : BitVec 64} (address : CodeAddr (modelOf I f r) a) : img I a :=
  BinaryBoundaryFacts.img_of_codeAddr (BinaryBoundaryFacts.of_returnPins checked) member address

end E2E.SemanticBinary
