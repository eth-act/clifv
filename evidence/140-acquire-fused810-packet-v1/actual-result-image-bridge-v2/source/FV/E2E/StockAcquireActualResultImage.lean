import FV.E2E.LinkCheck

namespace E2E.LinkCheck
open Backend Backend.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The code image contains the exact artifact from the actual result table. -/
theorem actual_results_code_image {R : Res}
    (names : ((progOf R).funcs.map (·.name)).Nodup)
    {f : Clif.Function} (member : f ∈ (progOf R).funcs) :
    ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default
      ((artOf R f).fb.program (artOf R f).base)) a → ImgT (tabOf R) a := by
  intro a address
  exact ⟨_, tab_mem names member, address⟩

end E2E.LinkCheck
