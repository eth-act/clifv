import FV.Backend.Proof.StockAcquireFrontierSourceOrder

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A pending group remains attached to its actual retained record. -/
theorem RecordFrontiers.member_group {f : Clif.Function} {ctx : Ctx} {records : List ScanRecord} {groups : List (List Nat)}
    (frontiers : RecordFrontiers f ctx records groups) {group : List Nat} (member : group ∈ groups) :
    ∃ record ∈ records,RecordFrontier f ctx record group := by
  induction frontiers with
  | nil => cases member
  | @cons record pending records groups head tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst group
      exact ⟨record,List.mem_cons_self ..,head⟩
    · obtain ⟨actual,present,frontier⟩ := ih member
      exact ⟨actual,List.mem_cons_of_mem _ present,frontier⟩

/-- Complete actual pending groups have strict reverse source order across all retained records. -/
theorem RecordFrontiers.flatten_source_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {records : List ScanRecord} {groups : List (List Nat)} (frontiers : RecordFrontiers f event.ctx records groups)
    (kept : ∀ record ∈ records,record ∈ event.output.records)
    (ordered : records.Pairwise (fun first second => ∀ color,first.output.state.color = some color →
      ∀ step,second.output.step = some step → step.decision = .emitted →
        ColorUpperBound color (scanState second.input second.inst))) :
    groups.flatten.Pairwise (fun first second => second < first) := by
  revert kept ordered
  induction frontiers with
  | nil => intro kept ordered;exact .nil
  | @cons record pending records groups head tail ih =>
    intro kept ordered
    have headMem := kept record (List.mem_cons_self ..)
    have tailKept : ∀ actual ∈ records,actual ∈ event.output.records :=
      fun actual member => kept actual (List.mem_cons_of_mem _ member)
    rw [List.flatten_cons]
    apply List.pairwise_append.mpr
    refine ⟨stock_lower_frontier_pending_order run events headMem head,ih tailKept (List.pairwise_cons.mp ordered).2,?_⟩
    intro first firstMem second secondMem
    obtain ⟨group,present,member⟩ := List.mem_flatten.mp secondMem
    obtain ⟨actual,actualMem,actualFrontier⟩ := tail.member_group present
    have relation := (List.pairwise_cons.mp ordered).1 actual actualMem
    exact stock_lower_frontier_pending_cross_order run events headMem (tailKept actual actualMem) relation
      head actualFrontier firstMem member

/-- Whole Stock scanning derives one general, duplicate-free source queue in exact reverse order. -/
theorem stock_lower_event_pending_source_queue_order {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ groups : List (List Nat),RecordFrontiers f event.ctx event.output.records groups ∧
      event.output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      groups.flatten.Pairwise (fun first second => second < first) ∧ groups.flatten.Nodup ∧
      groups.flatten.reverse.Pairwise (fun first second => first < second) ∧
      event.output.code.toList = event.output.records.reverse.flatMap (fun record => record.output.emitted.toList) := by
  obtain ⟨groups,frontiers,exactSunk,code⟩ := stock_lower_event_record_frontiers run events
  have ordered := stock_lower_event_record_pending_colors_order run scope events
  have queue := frontiers.flatten_source_order run events (fun record member => member) ordered
  have distinct : groups.flatten.Nodup := List.Pairwise.imp
    (fun {a b} less same => by subst b;omega) queue
  exact ⟨groups,frontiers,exactSunk,queue,distinct,List.pairwise_reverse.mpr queue,code⟩

end Backend.Stock.Proof.Acquire810
