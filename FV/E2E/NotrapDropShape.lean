import FV.E2E.OptX
import FV.Opt.Proof.NotrapDropSimU

/-!
# Dropping unused `notrap` loads keeps the shape (option D, #1017): `Opt.NotrapDrop.run_shape`

`E2E.ShapeFacts f (Opt.NotrapDrop.run f)`: the pass only filters block bodies, deleting
`Opt.removable` statements and `notrap` loads (never a call, a `call_indirect` or a terminator),
so it keeps the header, the signature declarations, the backend subset E, the callees, the
`try_call` callees, the indirect-call signatures and the presence of `return_call` and indirect
calls.
-/

namespace Opt.NotrapDrop

open Clif E2E

theorem keep_callIndirect {L : Std.HashSet ValueId} {st : Stmt} {sig : Nat} {c : ValueId}
    {args : List ValueId} (h : st.inst = .callIndirect sig c args) : keep L st = true := by
  simp [keep, droppable, h, removable, isPure, notrapLoad]

theorem dropWith_shape (f : Function) (L : Std.HashSet ValueId) : ShapeFacts f (dropWith f L) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, fun hE => ?_, fun fn hm => ?_, fun fn hm => ?_,
    fun i hm => ?_, fun hg => ?_, fun hg => ?_, fun hf => ?_⟩
  · simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at hE ⊢
    refine ⟨hE.1, fun b hb => ?_⟩
    rw [dropWith_blocks, List.mem_map] at hb
    obtain ⟨b0, hb0, rfl⟩ := hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hE.2 b0 hb0
    exact ⟨⟨h1, fun st hst => h2 st (List.mem_filter.1 hst).1⟩, h3⟩
  · simp only [callees, dropWith_blocks, List.flatMap_map, List.mem_flatMap,
      List.mem_filterMap] at hm ⊢
    obtain ⟨b, hb, st, hst, he⟩ := hm
    exact ⟨b, hb, st, (List.mem_filter.1 hst).1, he⟩
  · simpa [tryCallees, dropWith_blocks, List.filterMap_map, fltB] using hm
  · simp only [indSigIds, dropWith_blocks, List.flatMap_map, List.mem_flatMap, List.mem_append,
      List.mem_filterMap] at hm ⊢
    obtain ⟨b, hb, h⟩ := hm
    refine ⟨b, hb, ?_⟩
    rcases h with ⟨st, hst, he⟩ | h
    · exact .inl ⟨st, (List.mem_filter.1 hst).1, he⟩
    · exact .inr h
  · simpa [retCallFreeB, dropWith_blocks, fltB] using hg
  · simp only [indCallFreeB, dropWith_blocks, List.all_map, List.all_eq_true, Bool.and_eq_true,
      Function.comp_apply] at hg ⊢
    intro b hb
    obtain ⟨h1, h2⟩ := hg b hb
    refine ⟨fun st hst => ?_, h2⟩
    cases hi : st.inst with
    | callIndirect sig c args =>
      have := h1 st (List.mem_filter.2 ⟨hst, keep_callIndirect hi⟩)
      simp [hi] at this
    | _ => rfl
  · simp [dropWith_blocks, hf]

/-- **The pass keeps the shape.** -/
theorem run_shape (f : Function) : ShapeFacts f (run f) := by
  unfold run
  dsimp only
  split
  · exact dropWith_shape f _
  · exact ShapeFacts.refl f

end Opt.NotrapDrop
