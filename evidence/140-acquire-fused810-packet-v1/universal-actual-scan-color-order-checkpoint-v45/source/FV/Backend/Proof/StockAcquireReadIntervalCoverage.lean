import FV.Backend.Proof.StockAcquireMarkReadProvenance

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Each color consumed by an actual pending trace belongs to one of its actual sink targets. -/
theorem PendingSinks.color_covered {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) {final : Nat} (color : after.color = some final) :
    ∀ wanted,final ≤ wanted → wanted < final+pending.length →
      ∃ producer,producer ∈ pending ∧ before.entryColor[producer]! = wanted := by
  induction trace with
  | nil => intro wanted lower upper; simp only [List.length_nil] at upper; omega
  | @sink before middle after first rest actual tail ih =>
    have accepted := sink_accepted actual
    have entries : middle.entryColor = before.entryColor := by rw [accepted.2.2.2.2]
    have middleColor : middle.color = some before.entryColor[first]! := by rw [accepted.2.2.2.2]
    have firstColor : before.entryColor[first]! = final+rest.length :=
      Option.some.inj (middleColor.symm.trans (tail.color_distance color))
    intro wanted lower upper
    by_cases same : wanted = final+rest.length
    · exact ⟨first,List.mem_cons_self ..,firstColor.trans same.symm⟩
    · have smaller : wanted < final+rest.length := by simp only [List.length_cons] at upper; omega
      obtain ⟨producer,member,position⟩ := ih color wanted lower smaller
      exact ⟨producer,List.mem_cons_of_mem _ member,by simpa only [entries] using position⟩
  | frame entries unchanged tail ih =>
    intro wanted lower upper
    obtain ⟨producer,member,position⟩ := ih color wanted lower upper
    exact ⟨producer,member,by simpa only [entries] using position⟩

/-- Original metadata colors identify original source slots uniquely. -/
theorem source_color_equal_slots {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (first second : Nat) (firstSource : some first ∈ sourceColorEvents ctx ranges)
    (secondSource : some second ∈ sourceColorEvents ctx ranges)
    (same : (sourceMetadata ctx ranges).entryColor[first]! = (sourceMetadata ctx ranges).entryColor[second]!) :
    first = second := by
  have left := source_color_event_lookup built first firstSource
  have right := source_color_event_lookup built second secondSource
  rw [same] at left
  exact Option.some.inj (Option.some.inj (left.symm.trans right))

/-- Every original source effect in a consumed color interval belongs to the actual pending list. -/
theorem PendingMarks.source_interval_member {f : Clif.Function} {ctx original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState} {before after : State} {pending : List Nat}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : before.entryColor = (sourceMetadata original ranges).entryColor)
    (trace : PendingMarks ctx before pending after) {final : Nat} (color : after.color = some final)
    (producer : Nat) (source : some producer ∈ sourceColorEvents original ranges)
    (lower : final ≤ (sourceMetadata original ranges).entryColor[producer]!)
    (upper : (sourceMetadata original ranges).entryColor[producer]! < final+pending.length) : producer ∈ pending := by
  obtain ⟨actual,member,position⟩ := trace.forget.color_covered color _ lower upper
  have actualSource := trace.forget.source_members built metadata actual member
  rw [metadata] at position
  have same := source_color_equal_slots built actual producer actualSource source position
  rwa [same] at member

/-- The actual consumed interval derives successful source read frames without a supplied read certificate. -/
theorem ReadPendingMarks.source_interval_frame {f : Clif.Function} {ctx original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState} {before after : State} {pending : List Nat}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : before.entryColor = (sourceMetadata original ranges).entryColor)
    (trace : ReadPendingMarks ctx before pending after) {final : Nat} (color : after.color = some final)
    (producer : Nat) (source : some producer ∈ sourceColorEvents original ranges)
    (lower : final ≤ (sourceMetadata original ranges).entryColor[producer]!)
    (upper : (sourceMetadata original ranges).entryColor[producer]! < final+pending.length) :
    SourceReadFrame ctx producer :=
  trace.source_memory producer (trace.forget.source_interval_member built metadata color producer source lower upper)

end Backend.Stock.Proof.Acquire810
