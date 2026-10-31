import FV.Backend.Proof.StockReturnedSourceRetention
import FV.Backend.Proof.StockNoLoadDriver

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records,exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- An original store is retained and emitted in a source family without loads.
The original source shape supplies this family condition for singleton-store functions. -/
theorem stock_lower_store_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {j : Nat} {op : Clif.StoreOp} {ty : Clif.Ty} {flags : Clif.MemFlags} {value pointer : Nat} {offset : Int}
    (statement : b.body[j]? = some ⟨[],.store op ty flags value pointer offset⟩)
    {xs : List Nat} (ret : b.term = .ret xs) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step),
      SourceBodySplit f event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart f event.block+j ∧
      record.input.sunk[record.inst]! = false ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨term,body,termStep,split,member,unsunk,branch,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope events block (by rw [ret]; rfl)
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have indexed : blockStart f event.block+j ∈ sourceBodyIndices f event.block b := by
    unfold sourceBodyIndices
    apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr inside,rfl⟩
  rw [← split.scanned.order] at indexed
  obtain ⟨record,retained,current⟩ := List.mem_map.mp indexed
  obtain ⟨info,source,clif,infoResults⟩ :=
    ArithmeticBody.body_source_info run events split statement current
  have safeHere : record.input.sunk[record.inst]! = false :=
    (((SinkRules.stock_lower_no_load_unsunk run scope formats record.inst).2 event events).2
      record (split.retained record retained)).1
  have ordinary : record.inst ≠ event.termInst := by rw [current,split.termIndex]; omega
  have actual := scans_execute split.scanned record retained
  obtain ⟨step,decision,which⟩ := stock_ordinary_unsunk_decision safeHere ordinary actual
  have actualEmitted : step.decision = .emitted := by
    rcases which with omitted | remembered | emitted
    · have mandatory := (scan_omitted actual decision omitted).2.1
      simp [getElem!_def,source,clif,mustLower] at mandatory
    · exact False.elim ((Coverage.lower_record_noOpportunistic scope run events
        (split.retained record retained) decision) remembered)
    · exact emitted
  exact ⟨term,record,body,step,split,retained,current,safeHere,actual,
    split.retained record retained,decision,actualEmitted⟩

end Backend.Stock.Proof
