import FV.Concurrency.CallValid
import FV.Concurrency.ClifThreadIWitness

/-!
# Witness: the valid memory across a callee with a stack slot (#473, step (3))

The program of `ClifThreadIWitness` (`%f` calling `%g`, whose 8-byte slot the oracle places at
`0x7000 - 0xF0 + 0x10`), from the caller at depth 0 with memory `memW` (nothing allocated):

* `allocW`: after the call (`allocInvD_step`), `AllocInvD memW 0` holds although the slot is
  valid and `memW` has nothing valid there (`slotW`): the slot is a frame's above depth 0;
* `retW`: after `%g`'s `return`, back at depth 0 (`allocInvD_step`, `valid_of_allocInvD`), every
  valid range is `memW`'s — `resume_allA`'s `hval`.
-/

namespace Concurrency.CallValid.Witness

open Clif Concurrency.ClifThreadI.Witness

/-- The state after `%g`'s `return`. -/
def s2W : Clif.State := match Clif.step envW pW (sW memW) with
  | .next s => s
  | _ => sW memW

theorem factsV : B0W ∈ fW.blocks ∧ fW ∈ pW.funcs ∧
    (pW.funcs.all fun g => g.blocks.all fun b => match b.term with
      | .returnCall .. => false
      | _ => true) = true ∧
    isNext (Clif.step envW pW (sW memW)) = true ∧ (sW memW).callers.length = 1 ∧
    s2W.callers.length = 0 ∧
    (sW memW).mem.valid (0x7000 - 0xF0 + 0x10) 8 = true ∧ memW.valid (0x7000 - 0xF0 + 0x10) 8 = false ∧
    s2W.mem.valid (0x7000 - 0xF0 + 0x10) 8 = false := by
  native_decide

theorem linkFreeW : ∀ g ∈ pW.funcs, LinkFree g := by
  intro g hg b hb fn args he
  have h := factsV.2.2.1
  simp only [List.all_eq_true] at h
  have := h g hg b hb
  rw [he] at this
  cases this

theorem keepsW : EnvKeepsAllocs envW := by
  intro n g h
  simp [envW] at h
  cases h

theorem linvW : LInv pW (csW memW) :=
  ⟨⟨factsV.2.1, .inl ⟨B0W, factsV.1, List.suffix_refl _, rfl⟩⟩, fun _ h => nomatch h⟩

theorem stepW1 : Clif.step envW pW (csW memW) = .next (sW memW) := by
  have h := factsW.2.2.2.2.2.1
  unfold sW
  split
  · rename_i s hs; rw [hs]
  · rename_i hn; simp only [isNext] at h; cases h

theorem stepW2 : Clif.step envW pW (sW memW) = .next s2W := by
  have h := factsV.2.2.2.1
  unfold s2W
  split
  · rename_i s hs; rw [hs]
  · rename_i hn; simp only [isNext] at h; cases h

/-- **After the call, the slot is justified by the callee's frame** (module doc). -/
theorem allocW : AllocInvD memW 0 (sW memW) ∧ (sW memW).mem.valid (0x7000 - 0xF0 + 0x10) 8 = true ∧
    memW.valid (0x7000 - 0xF0 + 0x10) 8 = false :=
  ⟨allocInvD_step linkFreeW keepsW linvW (allocInvD_self _ 0) stepW1 (Nat.zero_le _)
    (Nat.zero_le _), factsV.2.2.2.2.2.2.1, factsV.2.2.2.2.2.2.2.1⟩

/-- **Back at depth 0 the valid ranges are the caller's** (module doc). -/
theorem retW : ∀ a k, s2W.mem.valid a k = true → memW.valid a k = true := by
  have hI := (step_next_linv linkFreeW linvW stepW1).1
  exact valid_of_allocInvD (allocInvD_step linkFreeW keepsW hI allocW.1 stepW2 (Nat.zero_le _)
    (Nat.zero_le _)) factsV.2.2.2.2.2.1

end Concurrency.CallValid.Witness
