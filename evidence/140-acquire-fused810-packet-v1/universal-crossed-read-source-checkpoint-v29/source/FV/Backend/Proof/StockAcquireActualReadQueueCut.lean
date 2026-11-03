import FV.Backend.Proof.StockAcquireReadQueueScans

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The empty actual scan has its original state and no invented records. -/
theorem ScansSpec.nil_inv {exec : Nat → State → Except String Scan} {input : State} {output : BlockScan}
    (spec : ScansSpec exec [] input output) : output = ⟨input,[],#[]⟩ := by cases spec; rfl

private theorem referenceCut_zero (colors : Array Nat) (inst : Nat) : referenceCut colors 0 inst = colors[inst]! := by
  unfold referenceCut
  split
  · rename_i zero
    exact zero.symm
  · rfl

/-- The real first unsunk terminator seeds the complete source-cut proof without an entry-color bound. -/
theorem ScansSpec.read_queue_from_term {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : ∀ record ∈ event.output.records,record.input.entryColor = (sourceMetadata original ranges).entryColor)
    {terminal : Nat} {indices : List Nat} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      (terminal::indices) event.input output)
    (kept : ∀ record ∈ output.records,record ∈ event.output.records)
    (notSunk : event.input.sunk[terminal]! = false)
    (reverse : indices.Pairwise (fun first second => second < first))
    (bounded : ColorTailBound (sourceMetadata original ranges).entryColor
      (sourceMetadata original ranges).entryColor[terminal]! indices) :
    ∃ groups : List (List Nat),RecordFrontiers f event.ctx output.records groups ∧
      output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      ReadQueueCut event.ctx original ranges
        ((terminal::indices).foldl (referenceCut (sourceMetadata original ranges).entryColor) 0)
        output.state groups.flatten := by
  obtain ⟨scan,tail,head,rest,equal⟩ := ScansSpec.cons_inv spec
  let record : ScanRecord := ⟨terminal,event.input,scan⟩
  have member : record ∈ event.output.records := by
    apply kept record
    rw [equal]
    exact List.mem_cons_self ..
  have entryColors := metadata record member
  have sunkBound : record.input.sunk[record.inst]! = true →
      referenceCut record.input.entryColor 0 record.inst ≤ 0 := by
    intro marked
    rw [notSunk] at marked
    cases marked
  obtain ⟨pending,frontier,after⟩ := stock_lower_record_read_queue_step run events member built entryColors
    (ReadQueueCut.zero event.ctx original ranges event.input) sunkBound
  have afterCut : ReadQueueCut event.ctx original ranges (sourceMetadata original ranges).entryColor[terminal]!
      scan.state pending := by
    simpa only [entryColors,referenceCut_zero,List.nil_append] using after
  have tailKept : ∀ retained ∈ tail.records,retained ∈ event.output.records := by
    intro retained member
    apply kept retained
    rw [equal]
    exact List.mem_cons_of_mem _ member
  obtain ⟨groups,frontiers,exactSunk,finished⟩ := ScansSpec.read_queue_progress run events built metadata rest
    (sourceMetadata original ranges).entryColor[terminal]! pending tailKept reverse bounded afterCut
  refine ⟨pending::groups,?_,?_,?_⟩
  · rw [equal]
    exact .cons frontier frontiers
  · rw [equal]
    rw [List.flatten_cons,List.foldl_append,← frontier.1]
    exact exactSunk
  · rw [equal]
    simpa only [List.foldl_cons,referenceCut_zero,List.flatten_cons] using finished

/-- Actual source ranges and the real terminator internally discharge every prefix cut/order obligation. -/
theorem stock_lower_scan_prefix_read_queue_cut {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {indices suffix : List Nat} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices event.input output)
    (parts : event.indices = indices++suffix)
    (kept : ∀ record ∈ output.records,record ∈ event.output.records) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (groups : List (List Nat)),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      event.input.entryColor = (sourceMetadata original ranges).entryColor ∧
      (∀ record ∈ event.output.records,record.input.entryColor = (sourceMetadata original ranges).entryColor) ∧
      RecordFrontiers f event.ctx output.records groups ∧
      output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      ReadQueueCut event.ctx original ranges
        (indices.foldl (referenceCut (sourceMetadata original ranges).entryColor) 0) output.state groups.flatten := by
  obtain ⟨original,ranges,initial,bi,block,built,blockAt,termEq,indicesEq,terminalSource,notSunk,entryColors,metadata⟩ :=
    stock_lower_event_cut_source run scope events
  cases indices with
  | nil =>
    have equal := ScansSpec.nil_inv spec
    refine ⟨original,ranges,initial,[],built,entryColors,metadata,?_,?_,?_⟩
    · rw [equal]; exact .nil
    · rw [equal]; rfl
    · rw [equal]
      simpa only [List.foldl_nil,List.flatten_nil] using ReadQueueCut.zero event.ctx original ranges event.input
  | cons first indices =>
    have compared := List.cons.inj (indicesEq.symm.trans parts)
    have firstEq : first = event.termInst := compared.1.symm
    subst first
    have bodyParts : ((Array.range block.body.length).map (blockStart f bi+·)).reverse.toList = indices++suffix := compared.2
    have reverse := scan_indices_reverse_order (blockStart f bi) block.body.length
    rw [bodyParts] at reverse
    have tailReverse := (List.pairwise_append.mp reverse).1
    have earlier : ∀ inst ∈ indices,inst < event.termInst := by
      intro inst member
      have bodyMember : inst ∈ ((Array.range block.body.length).map (blockStart f bi+·)).reverse.toList := by
        rw [bodyParts]
        exact List.mem_append_left _ member
      have bounds := scan_indices_bounds (blockStart f bi) block.body.length inst bodyMember
      rw [termEq]
      exact bounds.2
    have bounded := source_event_tail_bound built event.termInst terminalSource earlier
    obtain ⟨groups,frontiers,exactSunk,covered⟩ := ScansSpec.read_queue_from_term run events built metadata spec kept notSunk tailReverse bounded
    exact ⟨original,ranges,initial,groups,built,entryColors,metadata,frontiers,exactSunk,covered⟩

/-- Every complete actual Stock scan derives its queue and source cut without a caller color certificate. -/
theorem stock_lower_event_read_queue_cut {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) :
    ∃ (original : Ctx) (ranges : Array (Nat × Nat)) (initial : LState) (groups : List (List Nat)),
      Backend.buildCtx f = .ok (original,ranges,initial) ∧
      event.input.entryColor = (sourceMetadata original ranges).entryColor ∧
      (∀ record ∈ event.output.records,record.input.entryColor = (sourceMetadata original ranges).entryColor) ∧
      RecordFrontiers f event.ctx event.output.records groups ∧
      event.output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) event.input.sunk ∧
      ReadQueueCut event.ctx original ranges
        (event.indices.foldl (referenceCut (sourceMetadata original ranges).entryColor) 0) event.output.state groups.flatten := by
  exact stock_lower_scan_prefix_read_queue_cut run scope events (suffix := [])
    (runScans_spec (stock_lower_event_scan_run run events)) (by simp) (fun record member => member)

end Backend.Stock.Proof.Acquire810
