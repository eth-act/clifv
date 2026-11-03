import FV.Backend.Proof.StockAcquireRecordPendingOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original source metadata supplies the exact queue position of each source effect. -/
theorem source_color_event_lookup {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (producer : Nat) (member : some producer ∈ sourceColorEvents ctx ranges) :
    (sourceColorEvents ctx ranges)[(sourceMetadata ctx ranges).entryColor[producer]!]? = some (some producer) := by
  obtain ⟨pre,post,events⟩ := List.mem_iff_append.mp member
  rw [source_color_event_exact built pre post producer events,events]
  simp

/-- Every split of an actual pending trace has its exact descending source-color position. -/
theorem PendingMarks.color_at_split {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingMarks ctx before pending after) {final : Nat} (color : after.color = some final) :
    ∀ pre producer post,pending = pre++producer::post → before.entryColor[producer]! = final+post.length := by
  induction trace with
  | nil =>
    intro pre producer post impossible
    exact False.elim (by simpa using impossible)
  | @sink before middle after first rest actual tail ih =>
    intro pre producer post splitList
    have entries : middle.entryColor = before.entryColor := by rw [(sink_accepted actual).2.2.2.2]
    cases pre with
    | nil =>
      have equal := List.cons.inj splitList
      rcases equal with ⟨rfl,rfl⟩
      have middleColor : middle.color = some before.entryColor[first]! := by
        rw [(sink_accepted actual).2.2.2.2]
      exact Option.some.inj (middleColor.symm.trans (tail.forget.color_distance color))
    | cons x pre =>
      have equal := List.cons.inj splitList
      have found := ih color pre producer post equal.2
      rwa [entries] at found
  | frame entries unchanged sunk tail ih =>
    intro pre producer post splitList
    have found := ih color pre producer post splitList
    rwa [entries] at found

/-- Actual pending traces identify every original source event in their contiguous color interval. -/
theorem PendingMarks.source_event_at_split {f : Clif.Function} {ctx original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState} {before after : State} {pending : List Nat}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : before.entryColor = (sourceMetadata original ranges).entryColor)
    (trace : PendingMarks ctx before pending after) {final : Nat} (color : after.color = some final)
    (pre : List Nat) (producer : Nat) (post : List Nat) (splitList : pending = pre++producer::post) :
    (sourceColorEvents original ranges)[final+post.length]? = some (some producer) := by
  have member : producer ∈ pending := by rw [splitList]; simp
  have source := trace.forget.source_members built metadata producer member
  have found := source_color_event_lookup built producer source
  have position := trace.color_at_split color pre producer post splitList
  rw [metadata] at position
  rwa [position] at found

end Backend.Stock.Proof.Acquire810
