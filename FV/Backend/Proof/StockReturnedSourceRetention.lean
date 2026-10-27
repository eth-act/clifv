import FV.Backend.Proof.StockReturnedDefinitionRetention
import FV.Backend.Proof.StockPureRecordCoverage

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

/-- Every original definition requested by its block return is retained and
emitted, including nontrapping loads. Actual return demand protects the definition
through arbitrary intervening scans; omission and opportunistic reuse are excluded
by that demand and the original source scope. No global no-load premise is used. -/
theorem stock_lower_returned_definition_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    {z : Nat} (definition : z ∈ stm.results)
    {xs : List Nat} (ret : b.term = .ret xs) (returned : z ∈ xs) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step),
      SourceBodySplit f event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart f event.block+j ∧
      record.input.sunk[record.inst]! = false ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨term,body,termStep,split,member,unsunk,branch,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope events block (by rw [ret]; rfl)
  have defined : event.ctx.defInst? z = some (blockStart f event.block+j) :=
    stock_lower_source_result_definition run dominated events block statement definition
  have safe := stock_lower_return_demand_unsunk run scope events block ret member
    split.termInst recorded emitted returned defined
  have demanded := stock_lower_return_positive_demand run scope events block ret member
    split.termInst recorded emitted returned
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have indexed : blockStart f event.block+j ∈ sourceBodyIndices f event.block b := by
    unfold sourceBodyIndices
    apply List.mem_reverse.mpr
    exact List.mem_map.mpr ⟨j,List.mem_range.mpr inside,rfl⟩
  rw [← split.scanned.order] at indexed
  obtain ⟨record,retained,current⟩ := List.mem_map.mp indexed
  obtain ⟨info,source,clif,infoResults⟩ :=
    ArithmeticBody.body_source_info run events split statement current
  have original : event.ctx.insts[blockStart f event.block+j]? = some info := by
    rw [← current]; exact source
  have resultMember : z ∈ event.ctx.insts[blockStart f event.block+j]!.results := by
    simp only [getElem!_def,original,Option.getD_some,infoResults]
    exact definition
  obtain ⟨_,boundaries⟩ := stock_scans_demanded_unsunk split.scanned
  have kept := (boundaries record retained).1.2
    (blockStart f event.block+j) z resultMember demanded safe
  have safeHere : record.input.sunk[record.inst]! = false := by rw [current]; exact kept
  have ordinary : record.inst ≠ event.termInst := by rw [current,split.termIndex]; omega
  have actual := scans_execute split.scanned record retained
  obtain ⟨step,decision,which⟩ := stock_ordinary_unsunk_decision safeHere ordinary actual
  have actualEmitted : step.decision = .emitted := by
    rcases which with omitted | remembered | emitted
    · have zero := (scan_omitted actual decision omitted).2.2.1 z (by simpa only [current] using resultMember)
      have grows := (boundaries record retained).1.1 z
      exact False.elim (demanded (by omega))
    · exact False.elim ((Coverage.lower_record_noOpportunistic scope run events
        (split.retained record retained) decision) remembered)
    · exact emitted
  exact ⟨term,record,body,step,split,retained,current,safeHere,actual,
    split.retained record retained,decision,actualEmitted⟩

end Backend.Stock.Proof
