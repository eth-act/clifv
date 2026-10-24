import FV.Concurrency.CallSegT
import FV.Concurrency.PrivCohTWitness
import FV.Concurrency.ArmAllocEntry

/-!
# Witnesses for `CallSegT` (#473, step (4))

With the 8-byte slot at 100 masked (`U100`):

* `avoid_written`: the CLIF store to the slot and then a load of it read no masked byte (the
  store takes its bytes out of the mask);
* `cut_unwritten`: a load of the unwritten slot is the first step reading a masked byte
  (`readsAvoid_or_cut`'s second case, at step 0);
* `seg_nil`: `realizedT_seg` on the empty segment (start-dirty set the mask).
-/

namespace Concurrency.CallSegT.Witness

open Prog ClifThread ClifThreadI ThreadRefine CallComposeT PrivCohT.Witness ArmThread
  ArmAllocThread PrepThread

/-- The slot at 100, unwritten. -/
def U100 : Nat → Prop := fun a => 100 ≤ a ∧ a < 108

theorem avoid_written : ReadsAvoid U100 [[stS], [ldS]] := by
  refine ⟨fun e he => ?_, fun e he => ?_, trivial⟩
  · simp only [List.mem_singleton] at he; subst he; intro h; cases h
  · simp only [List.mem_singleton] at he
    subst he
    intro _ k hk hU
    exact hU.2 ⟨stS, List.mem_singleton_self _, rfl, by simp [stS, ldS],
      by simp only [stS, ldS] at hk ⊢; omega⟩

theorem cut_unwritten : ∃ j evs, [[ldS], [stS]][j]? = some evs ∧
    ReadsAvoid U100 ([[ldS], [stS]].take j) ∧ ReadsMasked (maskAfter U100 ([[ldS], [stS]].take j)) evs :=
  ⟨0, [ldS], rfl, trivial, ldS, List.mem_singleton_self _, rfl, 0, by simp [ldS],
    by simp [maskAfter, U100, ldS]⟩

theorem seg_nil (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (ls : List Lab) :
    RealizedT env p (fun _ => True) ls 0 (encT U100 (.run s)) (encT (maskAfter U100 []) (.run s))
      U100 (fun a => U100 a ∨ False) := by
  have href : Refines Maps (fun _ => False) (MonPair (evTr (ls.take 0))) ([] : List (List (Ev SKind BVal)))
      (conv (evTr (ls.take 0))) id := by
    simpa [evTr] using refines_privW (MK := Maps) (Priv := fun _ => False) (T := [])
      (fun q y hy => by simp [evAt] at hy)
  exact realizedT_seg (NS := fun _ => False) (Nat.zero_le _) .nil
    (by simpa [evTr] using CallCompose.xClosed_nil) href trivial (fun a h => .inr (.inl h))
    (fun _ _ _ _ h => by rw [evAt_nil] at h; cases h) (fun q x h => by rw [evAt_nil] at h; cases h)
    (fun q x h => by rw [evAt_nil] at h; cases h) (fun _ _ => trivial)

end Concurrency.CallSegT.Witness
