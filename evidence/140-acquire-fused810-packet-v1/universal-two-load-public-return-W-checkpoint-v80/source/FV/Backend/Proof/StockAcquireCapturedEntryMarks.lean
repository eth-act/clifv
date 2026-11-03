import FV.Backend.Proof.StockAcquireRetiredMarkFrontier

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Actual current-block source positions exclude inherited marks even before their color classification. -/
theorem stock_lower_body_slot_entry_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {block : Clif.Block} {index : Nat} {stm : Clif.Stmt}
    (blockAt : f.blocks[event.block]? = some block) (statement : block.body[index]? = some stm) :
    event.input.sunk[blockStart f event.block+index]! = false := by
  have bound := (List.getElem?_eq_some_iff.mp statement).1
  cases marked : event.input.sunk[blockStart f event.block+index]! with
  | false => rfl
  | true =>
    obtain ⟨owner,member,different,owned⟩ := stock_lower_entry_mark_other_block run scope events _ marked
    obtain ⟨actual,present,original,ranges,initial,otherBlock,built,otherAt,source⟩ := owned
    have sameOwner := List.mem_singleton.mp present
    subst actual
    have otherBounds := block_color_event_slot_bounds built otherAt source
    apply False.elim
    apply different
    rcases Nat.lt_trichotomy owner.block event.block with before | equal | after
    · have separated := block_layout_before f.blocks owner.block event.block otherBlock otherAt before
      simp only [blockStart_eq] at otherBounds
      omega
    · exact equal
    · have separated := block_layout_before f.blocks event.block owner.block block blockAt after
      simp only [blockStart_eq] at otherBounds
      omega

/-- Every actual captured read derives its own absent block-entry mark internally. -/
theorem stock_lower_captured_entry_unmarked {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {env : Clif.Env} {program : Clif.Program} (captured : SunkReadSnapshot event.ctx env program)
    (retained : captured.record ∈ event.output.records) : event.input.sunk[captured.record.inst]! = false := by
  obtain ⟨info,inst,values,regs,rest,installed,source,body,evaluated,written,frame⟩ := captured.source
  obtain ⟨block,index,stm,blockAt,statement,current,results⟩ :=
    stock_lower_source_record_body_position run scope events retained installed source
  rw [current]
  exact stock_lower_body_slot_entry_unsunk run scope events blockAt statement

end Backend.Stock.Proof.Acquire810
