import FV.Backend.Proof.StockAcquireGlobalEventOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every complete metadata event names an allocated source slot. -/
theorem source_color_event_inside {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (target : Nat) (member : some target ∈ sourceColorEvents ctx ranges) : target < ctx.insts.size := by
  have spec := ctxSpec_of built
  rw [sourceColorEvents,spec.func,List.mem_flatMap] at member
  obtain ⟨x,blockMember,eventMember⟩ := member
  have blockAt := List.mem_zipIdx_iff_getElem?.mp blockMember
  rcases (block_color_events_member built x.2 x.1 blockAt target).1 eventMember with body | term
  · obtain ⟨stm,index,statement,_,same⟩ := body
    obtain ⟨info,present,_,_⟩ := spec.facts.stmt x.2 x.1 index stm blockAt statement
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    omega
  · have present := spec.facts.term x.2 x.1 blockAt
    have inside := (Array.getElem?_eq_some_iff.mp present).1
    omega

/-- Actual source metadata never overwrites the slot of an earlier source event. -/
theorem source_color_event_no_overwrite {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (pre post : List (Option Nat)) (target : Nat)
    (events : sourceColorEvents ctx ranges = pre++some target::post) : some target ∉ post := by
  have ordered := source_color_event_order built
  rw [events] at ordered
  have headOrder := (List.pairwise_append.mp ordered).2.1
  have after := (List.pairwise_cons.mp headOrder).1
  intro repeated
  have impossible := after (some target) repeated target rfl target rfl
  omega

/-- A source color is its exact position in the complete original event queue. -/
theorem source_color_event_exact {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (pre post : List (Option Nat)) (target : Nat)
    (events : sourceColorEvents ctx ranges = pre++some target::post) :
    (sourceMetadata ctx ranges).entryColor[target]! = pre.length := by
  have member : some target ∈ sourceColorEvents ctx ranges := by
    rw [events]; exact List.mem_append_right _ (List.mem_cons_self ..)
  have inside := source_color_event_inside built target member
  have outside := source_color_event_no_overwrite built pre post target events
  rw [sourceMetadata_color_events,events]
  have exactValue := color_event_exact pre post (Array.replicate ctx.insts.size 0,0) target
    (by simpa using inside) outside
  simpa using exactValue

/-- Original source order determines the real metadata colors without caller bounds or certificates. -/
theorem source_color_event_pair_exact {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {initial : LState} (built : Backend.buildCtx f = .ok (ctx,ranges,initial))
    (pre mid post : List (Option Nat)) (first second : Nat)
    (events : sourceColorEvents ctx ranges = pre++some first::(mid++some second::post)) :
    (sourceMetadata ctx ranges).entryColor[first]! < (sourceMetadata ctx ranges).entryColor[second]! := by
  have firstValue := source_color_event_exact built pre (mid++some second::post) first events
  have same : (pre++some first::mid)++some second::post = pre++some first::(mid++some second::post) := by
    simp only [List.append_assoc,List.cons_append]
  have secondValue := source_color_event_exact built (pre++some first::mid) post second (events.trans same.symm)
  rw [firstValue,secondValue]
  simp only [List.length_append,List.length_cons]
  omega

end Backend.Stock.Proof.Acquire810
