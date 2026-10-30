import FV.Front.RenameRunX
import FV.E2E.LinkArmUProgWitness

/-!
# Witness: renaming a run that unwinds (S10f)

`E2E.LinkArmUProgWitness`'s whole-program run with unwinding from `f` on `41` unwinds (the extern
`throw` raises `77` through the program callee `h`). Under the renaming `swap` (`h` ↔ `k`, a
bijection that renames a function of the program), the renamed program in the renamed
environment unwinds with the same exception (`Clif.runLoopX_ren_unwound`), and `ArmRefinesU`
transfers across the renaming's erased outcomes (`Front.armRefinesU_erase`).
-/

namespace Front.RenameRunXWitness

open Clif E2E E2E.LinkArmUProgWitness

/-- Swap the names `h` and `k`. -/
def sw (x : String) : String := if x = "h" then "k" else if x = "k" then "h" else x

theorem sw_sw (x : String) : sw (sw x) = x := by
  unfold sw
  by_cases h1 : x = "h"
  · subst h1; decide
  · by_cases h2 : x = "k"
    · subst h2; decide
    · simp [h1, h2]

def swap : Ren := ⟨sw, sw, sw_sw, sw_sw⟩

/-- **The renamed run unwinds with the original exception.** -/
theorem renamed_unwinds :
    ∃ cs, initState (LU (fun _ => True)).P "f" [⟨.i64, 41#64⟩] {} = .ok cs ∧
      ∃ (e : Exn) (m : Mem), runLoopX (throwEnvX.ren swap) ((LU (fun _ => True)).P.rename swap.fwd) 10
          (cs.toX.ren swap) = .unwound e (m.ren swap) ∧ ExnRel e 77 := by
  obtain ⟨cs, hcs, e, m, hrun, hx⟩ := run_unwinds
  exact ⟨cs, hcs, e, m, runLoopX_ren_unwound swap _ _ _ _ hrun, hx⟩

/-- The renaming is not the identity on the program: `h` is a function of it. -/
theorem renames_h : ((LU (fun _ => True)).P.func? "h").isSome = true := by native_decide

end Front.RenameRunXWitness
