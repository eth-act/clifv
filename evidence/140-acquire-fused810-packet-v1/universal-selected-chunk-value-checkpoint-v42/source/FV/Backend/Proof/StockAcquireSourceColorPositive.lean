import FV.Backend.Proof.StockAcquireActualTrappedSliceMemory

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The original block boundary precedes every actual source event. -/
theorem source_color_event_nonzero {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (target : Nat) (member : some target ∈ sourceColorEvents ctx ranges) :
    (sourceMetadata ctx ranges).entryColor[target]! ≠ 0 := by
  have starts : (sourceColorEvents ctx ranges).head? = some none := by
    cases blocks : ctx.func.blocks with
    | nil => simp only [sourceColorEvents,blocks,List.zipIdx_nil,List.flatMap_nil] at member; cases member
    | cons block blocks =>
      simp only [sourceColorEvents,blocks,List.zipIdx_cons,List.flatMap_cons,blockColorEvents,
        List.cons_append,List.head?_cons]
  obtain ⟨pre,post,events⟩ := List.mem_iff_append.mp member
  rw [source_color_event_exact built pre post target events]
  intro zero
  have empty := List.length_eq_zero_iff.mp zero
  rw [events,empty,List.nil_append,List.head?_cons] at starts
  cases starts

end Backend.Stock.Proof.Acquire810
