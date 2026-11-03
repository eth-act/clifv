import FV.Backend.Proof.StockAcquireSourceEventIdentity
import FV.Backend.Proof.StockAcquirePendingOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every actual sink identifies a positive source effect, even in a general pending list. -/
theorem PendingSinks.member_positive {ctx : Ctx} {before after : State} {pending : List Nat}
    (trace : PendingSinks ctx before pending after) :
    ∀ producer ∈ pending, before.entryColor[producer]! ≠ 0 := by
  induction trace with
  | nil => simp
  | @sink before middle after producer rest actual tail ih =>
    have accepted := sink_accepted actual
    have entries : middle.entryColor = before.entryColor := by rw [accepted.2.2.2.2]
    intro target member
    rcases List.mem_cons.mp member with equal | restMember
    · simpa only [equal] using accepted.1
    · simpa only [entries] using ih target restMember
  | frame entries color tail ih =>
    intro target member
    simpa only [entries] using ih target member

/-- Positive metadata cannot name an event absent from the actual source queue. -/
theorem source_color_positive_member (ctx : Ctx) (ranges : Array (Nat × Nat)) (target : Nat)
    (positive : (sourceMetadata ctx ranges).entryColor[target]! ≠ 0) :
    some target ∈ sourceColorEvents ctx ranges := by
  apply Classical.byContradiction
  intro absent
  have kept := color_events_keeps_slot (sourceColorEvents ctx ranges)
    (Array.replicate ctx.insts.size 0,0) target absent
  rw [sourceMetadata_color_events] at positive
  have zero : (Array.replicate ctx.insts.size 0)[target]! = 0 := by
    by_cases inside : target < ctx.insts.size
    · simp [getElem!_def,Array.getElem?_replicate,inside]
    · simp [getElem!_def,Array.getElem?_replicate,inside]
  exact positive (kept.trans zero)

/-- Strict metadata order reflects actual source-slot order for all original effects. -/
theorem source_color_order_reflects_slots {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (ctx,ranges,initial)) (first second : Nat)
    (firstMember : some first ∈ sourceColorEvents ctx ranges)
    (secondMember : some second ∈ sourceColorEvents ctx ranges)
    (before : (sourceMetadata ctx ranges).entryColor[first]! <
      (sourceMetadata ctx ranges).entryColor[second]!) : first < second := by
  obtain ⟨pre,post,events⟩ := List.mem_iff_append.mp firstMember
  rw [events,List.mem_append,List.mem_cons] at secondMember
  rcases secondMember with earlier | equal | later
  · obtain ⟨left,right,splitPre⟩ := List.mem_iff_append.mp earlier
    have reversed : sourceColorEvents ctx ranges = left++some second::(right++some first::post) := by
      rw [events,splitPre]
      simp only [List.append_assoc,List.cons_append]
    have opposite := source_color_event_pair_exact built left right post second first reversed
    omega
  · have same : second = first := Option.some.inj equal
    subst second
    omega
  · have ordered := source_color_event_order built
    rw [events] at ordered
    have headOrder := (List.pairwise_append.mp ordered).2.1
    exact (List.pairwise_cons.mp headOrder).1 (some second) later first rfl second rfl

/-- Actual deferred sinks belong to the complete original source-event queue. -/
theorem PendingSinks.source_members {f : Clif.Function} {ctx original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState} {before after : State} {pending : List Nat}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : before.entryColor = (sourceMetadata original ranges).entryColor)
    (trace : PendingSinks ctx before pending after) :
    ∀ producer ∈ pending, some producer ∈ sourceColorEvents original ranges := by
  intro producer member
  have positive := trace.member_positive producer member
  rw [metadata] at positive
  exact source_color_positive_member original ranges producer positive

/-- The complete pending list runs in strict reverse original source-slot order. -/
theorem PendingSinks.source_order {f : Clif.Function} {ctx original : Ctx}
    {ranges : Array (Nat × Nat)} {initial : LState} {before after : State} {pending : List Nat}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : before.entryColor = (sourceMetadata original ranges).entryColor)
    (trace : PendingSinks ctx before pending after) {final : Nat} (color : after.color = some final) :
    pending.Pairwise (fun first second => second < first) := by
  apply List.Pairwise.imp_of_mem (p := trace.ordered color)
  intro first second firstMember secondMember before
  rw [metadata] at before
  exact source_color_order_reflects_slots built second first
    (trace.source_members built metadata second secondMember)
    (trace.source_members built metadata first firstMember) before

end Backend.Stock.Proof.Acquire810
