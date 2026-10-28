import FV.E2E.LinkPlaceBCount
import FV.E2E.LinkArmPlaceBWitness

/-!
# Witnesses for `LinkPlaceBCount.lean`

`LinkWitness`'s `f` (one slot) entered from `memB` (table `0xAB`, counter `0`), then two calls
advancing the counter by `2` and `3` (memories `cs.mem` with the counter set): the counter after
them is `0 + 1 + 2 + 3 = 6` (`counter_f`); `NextAdv.unique` pins the advances (`unique_ex`).
-/

namespace E2E.LinkPlaceBCountWitness

open Clif LinkWitness LinkArmPlaceBWitness LinkArmPlaceBWitness.InitB

/-- The memory `mem` with the counter of its oracle advanced by `e`. -/
def bump (mem : Mem) (e : Nat) : Mem :=
  { mem with place := mem.place.map fun pl => { pl with init := pl.init.map (·.adv e) } }

theorem nextAdv_bump (mem : Mem) (e : Nat) : NextAdv mem (bump mem e) e := by
  intro pl ini hp hi
  simp [bump, hp, hi]

def E : Nat → Nat := fun k => if k = 0 then 2 else 3

/-- The memories along the run: entry, after call `0`, after call `1`. -/
def ms (cs : State) : Nat → Mem
  | 0 => cs.mem
  | 1 => bump cs.mem 2
  | _ => bump (bump cs.mem 2) 3

theorem counter_f (F : BitVec 64 → Prop) : ∃ cs, initB = .ok cs ∧
    (L F).PlaceAtB (ms cs 2) (sp0 - BitVec.ofNat 64 (frameDrop ((L F).A fF).af))
      (LinkPlaceBWitness.ini0.adv 6) := by
  obtain ⟨cs, hi, -, -⟩ := initState_memB_f F
  have hs : fF.slots.isEmpty = false := by
    have := entryFacts.2.2.1
    simp only [frameB, Bool.and_eq_true, decide_eq_true_eq] at this
    cases h : fF.slots with
    | nil => have := this.2; rw [h] at this; cases this
    | cons _ _ => rfl
  refine ⟨cs, hi, ?_⟩
  have := (L F).counter_at entryFacts.2.2.2.1 hi (placeAtB_memB F) (ms cs) E rfl 2 (by
    intro k hk
    match k, hk with
    | 0, _ => exact nextAdv_bump _ 2
    | 1, _ => exact nextAdv_bump _ 3)
  simpa [LinkSys.slotted, hs, sumTo, E] using this

theorem unique_ex : ∀ e, NextAdv memB (bump memB 4) e → e = 4 :=
  fun e h => h.unique (nextAdv_bump memB 4) rfl rfl

end E2E.LinkPlaceBCountWitness
