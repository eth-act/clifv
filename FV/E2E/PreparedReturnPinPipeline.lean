import FV.E2E.SemanticPreparedMetadata
import FV.E2E.ReturnPinCheckFast

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Return compatibility uses only actual program metadata, not the base environment or world. -/
def returnPinChecks (I : LinkInput) (R : Res) (g : Clif.Function) : Bool :=
  (ofRes I R closedBase (fun _ => False)).returnPinsB g

theorem returnPinChecks_eq (I : LinkInput) (R : Res) (B : BaseEnv)
    (F : BitVec 64 → Prop) (g : Clif.Function) :
    returnPinChecks I R g = (ofRes I R B F).returnPinsB g := rfl

/-- Preserve every old check and derive physical result compatibility from the actual artifacts. -/
def okRReturnPins (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  okRSemanticFor Stock.MemorySretCopy.check stage I R &&
    (progOf R).funcs.all (returnPinChecks I R)

/-- The complete ABI-aware contract follows from executable checks and real pipeline observations. -/
theorem semanticPreparedReturnPinsResults_sound (stage : Clif.Function → VCode → VCode)
    {I : LinkInput} {R : Res}
    (hstage : stage = (fun _ => id) ∨ stage = (fun _ => DeadCleanup.prune))
    (hR : PreparedResults stage I R) (hI : okRReturnPins stage I R = true)
    {B : BaseEnv} {F : BitVec 64 → Prop} (hB : BaseOk (ofRes I R B F))
    (hF : ∀ a,(ofRes I R B F).Img a → F a) : (ofRes I R B F).OkSemanticReturnPins := by
  simp only [okRReturnPins,Bool.and_eq_true,List.all_eq_true] at hI
  have metadata := semanticPreparedMetadata_sound Stock.MemorySretCopy.check stage hR hI.1 hB hF
  refine metadata.toReturnPins fun g hg => ?_
  have facts := semanticPreparedFactsFor Stock.MemorySretCopy.check stage hR hI.1 hg
  have lower : SemanticABI.check g (artOf R g).vc = true := facts.lowerOk
  have pins : (ofRes I R B F).returnPinsB g = true := by
    rw [← returnPinChecks_eq]
    exact hI.2 g hg
  obtain ⟨prepared,alloc,emit,layout,_⟩ := facts.pipe
  rcases hstage with rfl | rfl
  · exact CompiledProgramReturnPins.of_checks (cleanup := false) lower prepared facts.prepOk
      facts.check alloc emit layout pins
  · exact CompiledProgramReturnPins.of_checks (cleanup := true) lower prepared facts.prepOk
      facts.check alloc emit layout pins

/-- Build the physical return cache once, then reuse it for every program function. -/
def okRReturnPinsFast (stage : Clif.Function → VCode → VCode) (I : LinkInput) (R : Res) : Bool :=
  okRSemanticFor Stock.MemorySretCopy.check stage I R &&
    let C := ReturnPinCtx.of I R
    (progOf R).funcs.all (returnPinsWith C)

@[csimp] theorem okRReturnPins_eq_fast : @okRReturnPins = @okRReturnPinsFast := by
  funext stage I R
  unfold okRReturnPins okRReturnPinsFast
  dsimp only
  rw [show returnPinsWith (ReturnPinCtx.of I R) = returnPinChecks I R from
    funext (returnPinsWith_of I R)]

end E2E.LinkCheck
