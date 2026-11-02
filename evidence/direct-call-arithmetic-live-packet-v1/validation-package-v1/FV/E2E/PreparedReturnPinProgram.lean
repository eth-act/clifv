import FV.E2E.PreparedReturnPinPipeline
import FV.E2E.LinkReturnPinGood

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The existing program statement applies to the actual checked artifacts in every valid world. -/
def CrateStmtReturnPins (I : LinkInput) (R : Res) (name : String) : Prop :=
  ∀ (B : BaseEnv) (F : BitVec 64 → Prop), BaseOk (ofRes I R B F) →
    (∀ a,(ofRes I R B F).Img a → F a) → ProgStmt (ofRes I R B F) name

/-- Executable checks and pipeline observations supply every program premise internally. -/
theorem preparedReturnPins_correct (stage : Clif.Function → VCode → VCode)
    {I : LinkInput} {R : Res}
    (hstage : stage = (fun _ => id) ∨ stage = (fun _ => DeadCleanup.prune))
    (prepared : PreparedResults stage I R) (checked : okRReturnPins stage I R = true)
    (name : String) : CrateStmtReturnPins I R name := by
  intro B F base world f found M ra s w₀ args cs entry room frame free image body arguments source
    avoids relation placement traps
  exact backend_correct_program_return_pins _
    (semanticPreparedReturnPinsResults_sound stage hstage prepared checked base world)
    (Clif.Program.func?_some found).1 M entry room frame free image body arguments source
    avoids relation placement traps

end E2E.LinkCheck
