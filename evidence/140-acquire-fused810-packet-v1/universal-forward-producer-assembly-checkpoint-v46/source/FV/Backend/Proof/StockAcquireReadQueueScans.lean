import FV.Backend.Proof.StockAcquireActualCutSource

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A real nonempty scan specification exposes its first call and the exact remaining scan. -/
theorem ScansSpec.cons_inv {exec : Nat → State → Except String Scan} {inst : Nat} {indices : List Nat}
    {input : State} {output : BlockScan} (spec : ScansSpec exec (inst::indices) input output) :
    ∃ (scan : Scan) (tail : BlockScan),exec inst input = .ok scan ∧ ScansSpec exec indices scan.state tail ∧
      output = ⟨tail.state,⟨inst,input,scan⟩::tail.records,tail.code++scan.emitted⟩ := by
  cases spec with
  | cons head rest => exact ⟨_,_,head,rest,rfl⟩

/-- Actual reverse scans derive queue coverage while the original reference cut moves backward. -/
theorem ScansSpec.read_queue_progress {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {original : Ctx} {ranges : Array (Nat × Nat)} {initial : LState}
    (built : Backend.buildCtx f = .ok (original,ranges,initial))
    (metadata : ∀ record ∈ event.output.records,record.input.entryColor = (sourceMetadata original ranges).entryColor)
    {indices : List Nat} {before : State} {output : BlockScan}
    (spec : ScansSpec (fun inst state => scanInstruction event.ctx event.block inst event.termInst event.isBranch state)
      indices before output) :
    ∀ (cut : Nat) (queue : List Nat),
      (∀ record ∈ output.records,record ∈ event.output.records) →
      indices.Pairwise (fun first second => second < first) →
      ColorTailBound (sourceMetadata original ranges).entryColor cut indices →
      ReadQueueCut event.ctx original ranges cut before queue →
      ∃ groups : List (List Nat),RecordFrontiers f event.ctx output.records groups ∧
        output.state.sunk = groups.flatten.foldl (fun bits producer => bits.set! producer true) before.sunk ∧
        ReadQueueCut event.ctx original ranges
          (indices.foldl (referenceCut (sourceMetadata original ranges).entryColor) cut) output.state (queue++groups.flatten) := by
  induction spec with
  | nil input =>
    intro cut queue kept reverse bounded covered
    refine ⟨[],.nil,rfl,?_⟩
    simpa only [List.foldl_nil,List.flatten_nil,List.append_nil] using covered
  | @cons inst indices before scan tail head rest ih =>
    intro cut queue kept reverse bounded covered
    let record : ScanRecord := ⟨inst,before,scan⟩
    have member : record ∈ event.output.records := kept record (List.mem_cons_self ..)
    have entryColors := metadata record member
    have bounds := referenceCut_tail_bound (source_metadata_positive_order built) reverse bounded
    have sunkBound : record.input.sunk[record.inst]! = true →
        referenceCut record.input.entryColor cut record.inst ≤ cut := by
      intro marked
      simpa only [entryColors] using bounds.1
    obtain ⟨pending,frontier,after⟩ := stock_lower_record_read_queue_step run events member
      built entryColors covered sunkBound
    have afterCut : ReadQueueCut event.ctx original ranges
        (referenceCut (sourceMetadata original ranges).entryColor cut inst) scan.state (queue++pending) := by
      simpa only [entryColors] using after
    obtain ⟨groups,frontiers,exactSunk,finished⟩ := ih
      (referenceCut (sourceMetadata original ranges).entryColor cut inst) (queue++pending)
      (fun retained member => kept retained (List.mem_cons_of_mem _ member))
      (List.pairwise_cons.mp reverse).2 bounds.2 afterCut
    refine ⟨pending::groups,.cons frontier frontiers,?_,?_⟩
    · rw [List.flatten_cons,List.foldl_append,← frontier.1]
      exact exactSunk
    · simpa only [List.foldl_cons,List.flatten_cons,List.append_assoc] using finished

end Backend.Stock.Proof.Acquire810
