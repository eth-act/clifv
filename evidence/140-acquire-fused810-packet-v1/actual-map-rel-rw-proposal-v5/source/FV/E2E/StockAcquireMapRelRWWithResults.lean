import FV.ArmFault.Step
import FV.E2E.OutsideAvoids
import FV.E2E.StockAcquireActualResultImage

namespace E2E.StockAcquirePending
open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupExecBytes
set_option autoImplicit false
set_option Elab.async false

/-- The original read/write mapping contract uses the actual result table's code image. -/
structure MapRelRWWithResults (mp : ArmFault.MemMap) (results : Res) (f : Clif.Function) (N : Nat)
    (r : Arm.ArmState) (args : List Clif.Val) (cm : Clif.Mem) : Prop where
  nw : OutsideAvoids (fun a => (mp a).allows .W = false) f N r args cm
  code : ∀ a, ImgT (tabOf results) a → (mp a).allows .R = true

/-- Actual function membership derives readable instruction and data-word bytes. -/
theorem mapRelRW_actual_code_readable {mp : ArmFault.MemMap} {results : Res} {f : Clif.Function} {N : Nat}
    {r : Arm.ArmState} {args : List Clif.Val} {cm : Clif.Mem}
    (mapped : MapRelRWWithResults mp results f N r args cm)
    (names : ((progOf results).funcs.map (·.name)).Nodup) (member : f ∈ (progOf results).funcs) :
    ∀ a, CodeAddr (Arm.set_program Arm.ArmState.default
      ((artOf results f).fb.program (artOf results f).base)) a → (mp a).allows .R = true := by
  intro a code
  exact mapped.code a (actual_results_code_image names member a code)

end E2E.StockAcquirePending
