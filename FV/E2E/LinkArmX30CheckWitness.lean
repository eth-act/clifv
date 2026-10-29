module

public import FV.E2E.LinkArmX30Check
public import FV.E2E.NonVacuityLink

@[expose] public section

/-!
# Non-vacuity of the `x30` check

`x30Free_all`: every compiled function of `LinkWitness`'s program passes `FnAsm.x30Free`
(`g` calls `h`, so its code has the frame-record pair and a `bl`). `g_has_checked_line`: `g`'s
code has a non-exempt instruction line, where `decX30Free_of_check` applies. `add_x30_rejected`:
the check rejects a line that writes `x30`.
-/

namespace E2E.LinkWitness

open Backend

theorem x30Free_all :
    P.funcs.all (fun g => (A g).fa.x30Free (getOk (labelOffsets (A g).fa.lines))) = true := by
  native_decide

theorem g_has_checked_line :
    ((A fG).fa.lines.toList.any fun ln => match ln with
      | .ins x _ => !x.x30Exempt
      | _ => false) = true := by
  native_decide

theorem add_x30_rejected :
    (Insn.aluRRR .add true (.x 30) (.x 0) (.x 1)).x30Ok ⟨0, fun _ => none⟩ = false := by
  native_decide

end E2E.LinkWitness
