import FV.E2E.LinkReturnPinGood
import FV.E2E.LinkReturnPinsWitness

namespace E2E.LinkReturnPinGoodWitness
open Backend Backend.Proof Backend.Proof.Driver LinkWitness
set_option autoImplicit false
set_option Elab.async false

/-- The complete shared per-state theorem applies to the actual linked fixture.
The fixture makes a successful source call with the nonzero result42. -/
theorem successful_program_states_witness :
    ∃ (system : LinkSys) (κ : Nat → Clif.Function → Nat) (memory : Clif.Mem)
      (cs : Clif.State) (cm : Clif.Mem),
      system.OkReturnPins (fun _ => .ordinary) ∧ system.Budget κ ∧
      (∀ M,system.ThmXReturnPins (fun _ => .ordinary) κ M) ∧
      Clif.initState system.P fH.name [⟨.i64,41⟩] memory = .ok cs ∧
      system.crun 3 cs = .returned [⟨.i64,42⟩] cm := by
  obtain ⟨old,cs,cm,_,_,entered,returned,_,_,_,_⟩ :=
    LinkReturnPinsWitness.successful_program_call_witness
  have original : (L fun _ => True).Ok := L_ok _ (fun _ _ => trivial)
  haveI : (L fun _ => True).std.CrunOk := (L fun _ => True).crunOk_std original
  have checked := old.toSemanticNI.toReturnPins
  have budget := LinkSys.budget_K_return_pins _ checked
  exact ⟨_,_,_,cs,cm,checked,budget,LinkSys.thmX_return_pins _ checked budget,entered,returned⟩

end E2E.LinkReturnPinGoodWitness
