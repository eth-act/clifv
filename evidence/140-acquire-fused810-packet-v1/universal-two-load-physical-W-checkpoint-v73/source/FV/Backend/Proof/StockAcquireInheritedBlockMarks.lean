import FV.Backend.Proof.StockAcquireScanBlocksUnique

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original block events stay inside their allocated source-slot interval. -/
theorem block_color_event_slot_bounds {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (ctx,ranges,initial)) {bi producer : Nat} {block : Clif.Block}
    (blockAt : f.blocks[bi]? = some block) (member : some producer ∈ blockColorEvents ranges (block,bi)) :
    blockStart f bi ≤ producer ∧ producer ≤ blockStart f bi+block.body.length := by
  rcases (block_color_events_member built bi block blockAt producer).mp member with
    ⟨stm,index,statement,colored,position⟩ | terminal
  · have bound := (List.getElem?_eq_some_iff.mp statement).1
    omega
  · omega

/-- The same original source event cannot belong to two different blocks. -/
theorem block_color_event_owner_unique {f : Clif.Function}
    {leftCtx rightCtx : Ctx} {leftRanges rightRanges : Array (Nat × Nat)} {leftInitial rightInitial : LState}
    (leftBuilt : Backend.buildCtx f = .ok (leftCtx,leftRanges,leftInitial))
    (rightBuilt : Backend.buildCtx f = .ok (rightCtx,rightRanges,rightInitial))
    {first second producer : Nat} {left right : Clif.Block}
    (leftAt : f.blocks[first]? = some left) (rightAt : f.blocks[second]? = some right)
    (leftMember : some producer ∈ blockColorEvents leftRanges (left,first))
    (rightMember : some producer ∈ blockColorEvents rightRanges (right,second)) : first = second := by
  have leftBounds := block_color_event_slot_bounds leftBuilt leftAt leftMember
  have rightBounds := block_color_event_slot_bounds rightBuilt rightAt rightMember
  rcases Nat.lt_trichotomy first second with before | equal | after
  · have separated := block_layout_before f.blocks first second left leftAt before
    simp only [blockStart_eq] at leftBounds rightBounds
    omega
  · exact equal
  · have separated := block_layout_before f.blocks second first right rightAt after
    simp only [blockStart_eq] at leftBounds rightBounds
    omega

/-- Every inherited mark has an actual earlier owner in a different original block. -/
theorem stock_lower_entry_mark_other_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    (producer : Nat) (marked : event.input.sunk[producer]! = true) :
    ∃ owner ∈ result.blockScans.toList,owner.block ≠ event.block ∧ SinkOwnedBy f [owner] producer := by
  obtain ⟨earlier,later,parts,owners⟩ := (stock_lower_all_sink_owners run scope).2 event events
  obtain ⟨owner,member,original,ranges,initial,block,built,blockAt,source⟩ := owners producer marked
  have unique := (stock_lower_scan_block_projection run scope).2
  have pairs : result.blockScans.toList.Pairwise (fun first second => first.block ≠ second.block) := List.pairwise_map.mp unique
  rw [parts] at pairs
  have different := (List.pairwise_append.mp pairs).2.2 owner member event (List.mem_cons_self ..)
  refine ⟨owner,?_,different,owner,List.mem_singleton_self _,original,ranges,initial,block,built,blockAt,source⟩
  rw [parts]
  exact List.mem_append_left _ member

/-- Current-block original source effects cannot carry inherited marks from another recorded block. -/
theorem stock_lower_current_block_entry_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState} {block : Clif.Block}
    (built : Backend.buildCtx f = .ok (original,ranges,initial)) (blockAt : f.blocks[event.block]? = some block)
    {producer : Nat} (source : some producer ∈ blockColorEvents ranges (block,event.block)) :
    event.input.sunk[producer]! = false := by
  cases marked : event.input.sunk[producer]! with
  | false => rfl
  | true =>
    obtain ⟨owner,member,different,owned⟩ := stock_lower_entry_mark_other_block run scope events producer marked
    obtain ⟨actual,present,other,otherRanges,otherInitial,otherBlock,otherBuilt,otherAt,otherSource⟩ := owned
    have sameOwner := List.mem_singleton.mp present
    subst actual
    exact False.elim (different (block_color_event_owner_unique otherBuilt built otherAt blockAt otherSource source))

/-- The selected producer's entry mark is excluded internally while all other inherited marks remain. -/
theorem stock_lower_acquire_entry_producer_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    (R : SourceEndpointReceipt f event record) : event.input.sunk[R.producer]! = false := by
  apply stock_lower_current_block_entry_unsunk run scope events R.built R.blockAt
  apply (block_color_events_member R.built event.block R.block R.blockAt R.producer).mpr
  exact Or.inl ⟨R.producerStmt,R.producerIndex,R.producerAt,by rw [R.atomic];rfl,R.position⟩

end Backend.Stock.Proof.Acquire810
