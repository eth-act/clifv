import FV.Backend.Proof.StockAcquireAllReadMarked

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An internal source cut names every crossed effect in the actual general read queue. -/
def ReadQueueCut (ctx original : Ctx) (ranges : Array (Nat × Nat)) (cut : Nat) (state : State)
    (queue : List Nat) : Prop :=
  (∀ final,state.color = some final → ∀ producer,some producer ∈ sourceColorEvents original ranges →
    final ≤ (sourceMetadata original ranges).entryColor[producer]! →
    (sourceMetadata original ranges).entryColor[producer]! < cut → producer ∈ queue) ∧
  ∀ producer ∈ queue,SourceReadFrame ctx producer

/-- The zero reference cut starts with an empty queue for every original entry state. -/
theorem ReadQueueCut.zero (ctx original : Ctx) (ranges : Array (Nat × Nat)) (state : State) :
    ReadQueueCut ctx original ranges 0 state [] := by
  constructor
  · intro final color producer source lower upper
    omega
  · simp

/-- Changes outside the active color preserve the complete derived queue coverage. -/
theorem ReadQueueCut.of_color_eq {ctx original : Ctx} {ranges : Array (Nat × Nat)} {cut : Nat}
    {before after : State} {queue : List Nat} (covered : ReadQueueCut ctx original ranges cut before queue)
    (same : after.color = before.color) : ReadQueueCut ctx original ranges cut after queue := by
  refine ⟨?_,covered.2⟩
  intro final color producer source lower upper
  exact covered.1 final (same.symm.trans color) producer source lower upper

/-- Moving the original source cut backward preserves coverage without assuming color is below the cut. -/
theorem ReadQueueCut.shrink {ctx original : Ctx} {ranges : Array (Nat × Nat)} {beforeCut afterCut : Nat}
    {state : State} {queue : List Nat} (covered : ReadQueueCut ctx original ranges beforeCut state queue)
    (smaller : afterCut ≤ beforeCut) : ReadQueueCut ctx original ranges afterCut state queue := by
  refine ⟨?_,covered.2⟩
  intro final color producer source lower upper
  exact covered.1 final color producer source lower (by omega)

/-- Actual interpreter execution appends precisely the new read group to the existing covered frontier. -/
theorem ReadQueueCut.append_execution {f : Clif.Function} {ctx original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState} {before after : State} {cut : Nat} {queue pending : List Nat}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : before.entryColor = (sourceMetadata original ranges).entryColor)
    (covered : ReadQueueCut ctx original ranges cut before queue)
    (trace : ReadPendingMarks ctx before pending after) :
    ReadQueueCut ctx original ranges cut after (queue++pending) := by
  constructor
  · intro final color producer source lower upper
    have start := trace.forget.forget.color_distance color
    by_cases recent : (sourceMetadata original ranges).entryColor[producer]! < final+pending.length
    · exact List.mem_append_right _ (trace.forget.source_interval_member built metadata color producer source lower recent)
    · exact List.mem_append_left _ (covered.1 _ start producer source (by omega) upper)
  · intro producer member
    rcases List.mem_append.mp member with inherited | current
    · exact covered.2 producer inherited
    · exact trace.source_memory producer current

/-- A real colored reset derives coverage at its exact source cut before appending its read group. -/
theorem ReadQueueCut.reset_execution {f : Clif.Function} {ctx original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState} {earlier before after : State}
    {oldCut cut : Nat} {queue pending : List Nat}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : before.entryColor = (sourceMetadata original ranges).entryColor)
    (prior : ReadQueueCut ctx original ranges oldCut earlier queue)
    (colorBefore : before.color = some cut) (trace : ReadPendingMarks ctx before pending after) :
    ReadQueueCut ctx original ranges cut after (queue++pending) := by
  constructor
  · intro final color producer source lower upper
    have start := trace.forget.forget.color_distance color
    have exactCut : cut = final+pending.length := Option.some.inj (colorBefore.symm.trans start)
    rw [exactCut] at upper
    exact List.mem_append_right _ (trace.forget.source_interval_member built metadata color producer source lower upper)
  · intro producer member
    rcases List.mem_append.mp member with inherited | current
    · exact prior.2 producer inherited
    · exact trace.source_memory producer current

/-- A covered source effect derives its successful source memory frame from the actual queue. -/
theorem ReadQueueCut.source_read {ctx original : Ctx} {ranges : Array (Nat × Nat)} {cut final : Nat}
    {state : State} {queue : List Nat} (covered : ReadQueueCut ctx original ranges cut state queue)
    (color : state.color = some final) (producer : Nat)
    (source : some producer ∈ sourceColorEvents original ranges)
    (lower : final ≤ (sourceMetadata original ranges).entryColor[producer]!)
    (upper : (sourceMetadata original ranges).entryColor[producer]! < cut) : SourceReadFrame ctx producer :=
  covered.2 producer (covered.1 final color producer source lower upper)

end Backend.Stock.Proof.Acquire810
