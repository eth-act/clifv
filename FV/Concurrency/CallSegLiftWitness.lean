import FV.Concurrency.CallSegLift
import FV.Concurrency.CallSegTWitness

/-!
# Witnesses: an activation's segment lifted below a caller (#473, step (4))

* `prefix_nil`: `Refines.prefixNil` drops the trailing event-free step of `[[stS], []]`;
* `lift_nil`: `realizedT_lift` on the empty segment of any state, below a suspended caller
  frame, from the mask `U100` (the whole segment, realized from the lifted state).
-/

namespace Concurrency.CallSegLift.Witness

open Prog ClifThread ClifThreadI ThreadRefine CallComposeT PrivCohT.Witness ArmThread
  ArmAllocThread PrepThread CallSegT.Witness ClifLift

theorem prefix_nil : evAt ([[stS]] : List (List (Ev SKind BVal))) (0, 0) = some stS ∧
    ∀ q, evAt ([[stS]] : List (List (Ev SKind BVal))) q = evAt [[stS], []] q :=
  ⟨rfl, evAt_prefix_nil ⟨[[]], rfl⟩ (by simp)⟩

theorem lift_nil (env : Clif.Env) (p : Clif.Program) (s : Clif.State) (fr : Clif.Frame)
    (rs : List Clif.ValueId) (u : Arm.ArmState × Mon) :
    ∃ (trS' : List (List (Ev SKind BVal))) (s1 : Clif.State),
      RealizedT env p (fun _ => True) [] 0 (encT U100 (.run (pushC [(fr, rs)] s)))
        (encT (maskAfter U100 trS') (.run (pushC [(fr, rs)] s1))) U100
        (fun a => U100 a ∨ False) ∧ s1 = s := by
  have href : Refines Maps (fun _ => False) (MonPair (evTr (([] : List Lab).take 0)))
      ([] : List (List (Ev SKind BVal))) (conv (evTr (([] : List Lab).take 0))) id := by
    simpa [evTr] using refines_privW (MK := Maps) (Priv := fun _ => False) (T := [])
      (fun q y hy => by simp [evAt] at hy)
  rcases realizedT_lift (env := env) (p := p) (Bnd := fun _ => True) (f := id)
      (ok := fun _ _ => True) (u := u) (PRun.nil) (Nat.zero_le _) [(fr, rs)]
      (s := s) (t := .run s) .nil (by simpa [evTr] using CallCompose.xClosed_nil) href
      (NS := fun _ => False) (fun a h => .inr (.inl h))
      (fun _ _ _ _ h => by rw [evAt_nil] at h; cases h) (fun q x h => by rw [evAt_nil] at h; cases h)
      (fun q x h => by rw [evAt_nil] at h; cases h) (fun _ _ => trivial) with
    ⟨trS', s1, -, hR, hs, -⟩ | ⟨k', hk', trS', j, evs, hp, hj, -⟩
  · exact ⟨trS', s1, hR, hs s rfl⟩
  · obtain rfl : trS' = [] := List.eq_nil_of_prefix_nil hp
    cases hj

end Concurrency.CallSegLift.Witness
