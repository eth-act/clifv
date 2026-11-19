import FV.Opt.Proof.NotrapDropSim

/-!
# What the drop of unused `notrap` loads never deletes (option D, #1017)

* `run_keeps_trapping`: a load with a trap code (it can trap: `Mem.checkAccess`) is never deleted;
* `run_keeps_used`: a statement one of whose results the output reads (an operand of a statement
  of `run f`, or of a terminator) is never deleted, so in particular a `notrap` load whose value
  is used stays;
* `run_keeps_effects`: nor is any statement that is neither `Opt.removable` nor a `notrap` load
  (calls, stores, atomics, traps, …).
-/

namespace Opt.NotrapDrop

open Clif

/-- A statement `keep` accepts stays in its block. -/
theorem run_keeps {f : Function} {b : Block} (hb : b ∈ f.blocks) {st : Stmt} (hst : st ∈ b.body)
    (hk : ∀ L, keep L st = true) : ∃ b' ∈ (run f).blocks, b'.id = b.id ∧ st ∈ b'.body := by
  unfold run
  dsimp only
  split
  · exact ⟨fltB _ b, List.mem_map.2 ⟨b, hb, rfl⟩, rfl, List.mem_filter.2 ⟨hst, hk _⟩⟩
  · exact ⟨b, hb, rfl, hst⟩

/-- **Every statement other than a removable one or a `notrap` load stays.** -/
theorem run_keeps_effects {f : Function} {b : Block} (hb : b ∈ f.blocks) {st : Stmt}
    (hst : st ∈ b.body) (hd : droppable st.inst = false) :
    ∃ b' ∈ (run f).blocks, b'.id = b.id ∧ st ∈ b'.body :=
  run_keeps hb hst fun L => by simp [keep, hd]

/-- **A load with a trap code is never deleted.** -/
theorem run_keeps_trapping {f : Function} {b : Block} (hb : b ∈ f.blocks) {st : Stmt}
    (hst : st ∈ b.body) {op : LoadOp} {ty : Ty} {fl : MemFlags} {p : ValueId} {off : Int}
    (hi : st.inst = .load op ty fl p off) {c : TrapCode} (hc : fl.trapCode = some c) :
    ∃ b' ∈ (run f).blocks, b'.id = b.id ∧ st ∈ b'.body :=
  run_keeps_effects hb hst (by simp [droppable, hi, removable, isPure, notrapLoad, hc])

/-- **A statement whose result the output reads is never deleted.** -/
theorem run_keeps_used {f : Function} {b : Block} (hb : b ∈ f.blocks) {st : Stmt}
    (hst : st ∈ b.body) {r : ValueId} (hr : r ∈ st.results)
    (hu : ∃ b' ∈ (run f).blocks,
      (∃ st' ∈ b'.body, r ∈ operands st'.inst) ∨ r ∈ termOperands b'.term) :
    ∃ b' ∈ (run f).blocks, b'.id = b.id ∧ st ∈ b'.body := by
  revert hu
  unfold run
  dsimp only
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have hF := facts_of h.1.2 h.2
    intro hu
    obtain ⟨b', hb', hu⟩ := hu
    rw [dropWith_blocks, List.mem_map] at hb'
    obtain ⟨b0, hb0, rfl⟩ := hb'
    have hL : (live f).contains r = true := by
      rcases hu with ⟨st', hst', hx⟩ | hx
      · obtain ⟨hst0, hk⟩ := List.mem_filter.1 hst'
        exact hF.stmts b0 hb0 st' hst0 hk r hx
      · exact hF.terms b0 hb0 r hx
    have hk : keep (live f) st = true := by
      simp only [keep, Bool.or_eq_true, List.any_eq_true]
      exact .inr ⟨r, hr, hL⟩
    exact ⟨fltB _ b, List.mem_map.2 ⟨b, hb, rfl⟩, rfl, List.mem_filter.2 ⟨hst, hk⟩⟩
  · intro _
    exact ⟨b, hb, rfl, hst⟩

end Opt.NotrapDrop
