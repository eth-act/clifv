import FV.Backend.Proof.StockAcquireExecutedEffectBinding

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Every actual retained record has its own complete executed group. -/
theorem ExecutedRecordFrontiers.member_record {f : Clif.Function} {ctx : Ctx}
    {records : List ScanRecord} {groups : List (List Nat)} (frontiers : ExecutedRecordFrontiers f ctx records groups)
    {record : ScanRecord} (member : record ∈ records) :
    ∃ pending ∈ groups,ExecutedRecordFrontier f ctx record pending := by
  induction frontiers with
  | nil => cases member
  | @cons actual pending records groups head tail ih =>
    rcases List.mem_cons.mp member with equal | member
    · subst record
      exact ⟨pending,List.mem_cons_self ..,head⟩
    · obtain ⟨group,present,frontier⟩ := ih member
      exact ⟨group,List.mem_cons_of_mem _ present,frontier⟩

/-- The actual complete driver derives every selected acquire's exact queue group and final code segment. -/
theorem stock_lower_event_acquire_effect_bindings {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ groups : List (List Nat),ExecutedRecordFrontiers f event.ctx event.output.records groups ∧
      groups.flatten.Pairwise (fun first second => second < first) ∧
      ∀ record ∈ event.output.records,∀ step,record.output.step = some step → step.decision = .emitted →
        step.rules.getLast? = some 810 →
        ∃ (pending : List Nat) (R : SourceEndpointReceipt f event record)
          (pointerReg dest label index : Nat) (block : VBlock),
          pending ∈ groups ∧ pending = [R.producer] ∧ event.ctx.valueReg? R.pointer = some (.vreg pointerReg .int) ∧
          result.code.blocks[label]? = some block ∧
          SegAt block index [.loadAcquire (CTy.ofClif R.ty) (.vreg dest .int)
            (.vreg (aliasNum result.final.alias pointerReg) .int) R.flags] := by
  obtain ⟨groups,frontiers,exactSunk,ordered⟩ := stock_lower_event_executed_source_order run scope events
  refine ⟨groups,frontiers,ordered,?_⟩
  intro record records step recorded emitted selectedId
  obtain ⟨pending,member,frontier⟩ := frontiers.member_record records
  obtain ⟨R,pointerReg,dest,label,index,block,singleton,register,found,segment⟩ :=
    stock_lower_acquire_executed_effect_binding run scope dominated events records recorded emitted selectedId frontier
  exact ⟨pending,R,pointerReg,dest,label,index,block,member,singleton,register,found,segment⟩

end Backend.Stock.Proof.Acquire810
