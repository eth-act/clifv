import FV.E2E.RegLevelLeafKeep
import FV.E2E.NonVacuityLink

/-!
# Non-vacuity of the frameless leaf's `x29`/`x30` check (#1028, slice 2)

`faH0_leafKeep`: the leaf `h` of `LinkWitness`'s program, emitted without its frame (as
`Backend.frameless` leaves it under `preserve_frame_pointers=false`), passes `FnAsm.leafKeep`, and
has an unhooked instruction line other than `ret` (`faH0_has_checked_line`), where
`RL.step_gprKeep` uses the decoded-instruction case. The check rejects the same function with its
frame (`faH_framed_rejected`: the frame-record pair), the caller `g` (`faG_rejected`), and lines
that write `x30` or `x29` (`add_x30_rejected'`, `add_x29_rejected`).
-/

namespace E2E.LinkWitness

open Backend

/-- `h`, emitted without its frame. -/
def faH0 : FnAsm := getOk (emitFunc (A fH).k { (A fH).af with frame := false })

theorem faH0_leafKeep : faH0.leafKeep (getOk (labelOffsets faH0.lines)) = true := by
  native_decide

theorem faH0_has_checked_line :
    (faH0.lines.toList.any fun ln => match ln with
      | .ins x _ => !x.hooked && x != .ret
      | _ => false) = true := by
  native_decide

theorem faH_framed_rejected :
    (A fH).fa.leafKeep (getOk (labelOffsets (A fH).fa.lines)) = false := by
  native_decide

theorem faG_rejected :
    (A fG).fa.leafKeep (getOk (labelOffsets (A fG).fa.lines)) = false := by
  native_decide

theorem add_x30_rejected' :
    (Insn.aluRRR .add true (.x 30) (.x 0) (.x 1)).gprKeep 30#5 ⟨0, fun _ => none⟩ = false := by
  native_decide

theorem add_x29_rejected :
    (Insn.aluRRR .add true (.x 0) (.x 29) (.x 1)).gprKeep 29#5 ⟨0, fun _ => none⟩ = false := by
  native_decide

end E2E.LinkWitness
