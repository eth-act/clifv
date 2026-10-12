import FV.Backend.Proof.DeadCleanupSimulation
import FV.E2E.Statement

namespace Backend.DeadCleanup
open Backend.Proof Backend.Proof.Driver

/-- Identical entry stores establish the cleanup simulation without a new
source-side invariant or per-program execution certificate. -/
theorem rel_entry {V W : Type} {vc : VCode} {vb : VBlock}
    (hb : vc.blocks[0]? = some vb) (a : Nat → V) (w : W) :
    Rel vc (.run ⟨0, 0, a, w⟩) (.run ⟨0, 0, a, w⟩) := by
  apply Rel.run hb
  · simp [cleanBlock]
  · exact fun _ _ => rfl

private theorem entry_exists {V W : Type} {vc : VCode} {sem : ISem V W}
    {a : Nat → V} {w : W} {b k : Nat} {a1 : Nat → V} {w1 : W} {vb : VBlock}
    (hs : Star (VStep vc sem) (.run ⟨0, 0, a, w⟩) (.run ⟨b, k, a1, w1⟩))
    (hb : vc.blocks[b]? = some vb) : ∃ vb0, vc.blocks[0]? = some vb0 := by
  cases hs with
  | refl => exact ⟨vb, hb⟩
  | step h _ => cases h with | step he _ _ _ _ _ => exact ⟨_, he⟩

/-- Returns, including their ABI register list, operand values and world,
survive cleanup. -/
theorem returns_clean {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {a : Nat → CV} {w0 w : Arm.ArmState} {us : List (Reg × Reg)} {vals : List CV}
    (h : E2E.VReturns vc sem a w0 us vals w) :
    E2E.VReturns (clean vc) sem a w0 us vals w := by
  obtain ⟨b, k, a1, w1, vb, ops, outs, hstar, hb, hi, hop, hv, hs⟩ := h
  obtain ⟨vb0, hb0⟩ := entry_exists hstar hb
  obtain ⟨c1, hstar', hr⟩ := star_sim hp ht (rel_entry hb0 a w0) hstar
  obtain ⟨k', a', rfl, hb', hi', hu⟩ := rel_kept hr hb hi hop rfl
  refine ⟨b, k', a', w1, cleanBlock vc 0 vb, ops, outs, hstar', hb', hi', hop, ?_, hs⟩
  exact hv.trans hu

/-- Traps preserve the original trap code and instruction semantics. -/
theorem traps_clean {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true)
    {a : Nat → CV} {w0 : Arm.ArmState} {code : Clif.TrapCode}
    (h : E2E.VTraps vc sem a w0 code) :
    E2E.VTraps (clean vc) sem a w0 code := by
  obtain ⟨b, k, a1, w1, vb, i, ops, outs, w', hstar, hb, hi, hop, hs, hc⟩ := h
  have hkeep : pureForm i = false := by
    cases he : pureForm i
    · rfl
    · have hn := (hp _ _ _ _ _ _ he hs).2
      cases hn
  obtain ⟨vb0, hb0⟩ := entry_exists hstar hb
  obtain ⟨c1, hstar', hr⟩ := star_sim hp ht (rel_entry hb0 a w0) hstar
  obtain ⟨k', a', rfl, hb', hi', hu⟩ := rel_kept hr hb hi hop hkeep
  refine ⟨b, k', a', w1, cleanBlock vc 0 vb, i, ops, outs, w', hstar', hb', hi', hop, ?_, hc⟩
  rw [← hu]
  exact hs

/-- The new cleanup layer has the existing preparation-correctness interface. -/
theorem cleanup_correct {vc : VCode} {sem : Sem}
    (hp : ∀ i us w outs w' ctl, pureForm i = true →
      sem i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (ht : ∀ vb ∈ vc.blocks.toList, ∃ t, vb.insts.back? = some t ∧ t.isTerminator = true) :
    E2E.PrepareCorrect sem vc (clean vc) := by
  intro a w
  exact ⟨fun _ _ _ h => returns_clean hp ht h, fun _ h => traps_clean hp ht h⟩

end Backend.DeadCleanup
