import FV.Backend.Proof.StockAcquireSelectedOutputColor

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- This internal interval contains only real source effects and no intervening block boundary. -/
def SourceColorGap (original : Ctx) (ranges : Array (Nat × Nat)) (cut : Nat) (state : State) : Prop :=
  ∀ final,state.color = some final → ∀ wanted,final ≤ wanted → wanted < cut →
    ∃ producer,(sourceColorEvents original ranges)[wanted]? = some (some producer)

theorem SourceColorGap.zero (original : Ctx) (ranges : Array (Nat × Nat)) (state : State) :
    SourceColorGap original ranges 0 state := by
  intro final color wanted lower upper
  omega

theorem SourceColorGap.at_color {original : Ctx} {ranges : Array (Nat × Nat)} {cut : Nat} {state : State}
    (color : state.color = some cut) : SourceColorGap original ranges cut state := by
  intro final same wanted lower upper
  have equal := Option.some.inj (color.symm.trans same)
  omega

theorem SourceColorGap.of_color_eq {original : Ctx} {ranges : Array (Nat × Nat)} {cut : Nat}
    {before after : State} (covered : SourceColorGap original ranges cut before)
    (same : after.color = before.color) : SourceColorGap original ranges cut after := by
  intro final color wanted lower upper
  exact covered final (same.symm.trans color) wanted lower upper

theorem SourceColorGap.shrink {original : Ctx} {ranges : Array (Nat × Nat)} {beforeCut afterCut : Nat}
    {state : State} (covered : SourceColorGap original ranges beforeCut state)
    (smaller : afterCut ≤ beforeCut) : SourceColorGap original ranges afterCut state := by
  intro final color wanted lower upper
  exact covered final color wanted lower (by omega)

/-- Every consumed color comes from an actual source sink, including general pending lists. -/
theorem SourceColorGap.append_execution {f : Clif.Function} {ctx original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState} {before after : State} {cut : Nat} {pending : List Nat}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : before.entryColor = (sourceMetadata original ranges).entryColor)
    (covered : SourceColorGap original ranges cut before)
    (trace : PendingSinks ctx before pending after) : SourceColorGap original ranges cut after := by
  intro final color wanted lower upper
  have start := trace.color_distance color
  by_cases recent : wanted < final+pending.length
  · obtain ⟨producer,member,position⟩ := trace.color_covered color wanted lower recent
    have source := trace.source_members built metadata producer member
    have lookup := source_color_event_lookup built producer source
    rw [metadata] at position
    rw [position] at lookup
    exact ⟨producer,lookup⟩
  · exact covered _ start wanted (by omega) upper

/-- Real colored resets initialize an empty interval before the actual pending effects execute. -/
theorem SourceColorGap.reset_execution {f : Clif.Function} {ctx original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState} {before after : State} {cut : Nat} {pending : List Nat}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : before.entryColor = (sourceMetadata original ranges).entryColor)
    (color : before.color = some cut) (trace : PendingSinks ctx before pending after) :
    SourceColorGap original ranges cut after :=
  SourceColorGap.append_execution built metadata (SourceColorGap.at_color color) trace

end Backend.Stock.Proof.Acquire810
