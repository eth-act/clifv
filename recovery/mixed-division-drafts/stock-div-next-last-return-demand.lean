import FV.Backend.Proof.StockDivReturnDemand
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The final returned division is retained even after an arbitrary source
prefix. Its input is exactly the real return-request output, so retention does
not require a whole-body no-sinking certificate. -/
theorem stock_lower_last_div_return_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z]) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step),
      SourceBodySplit f event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart f event.block + front.length ∧ record.input = term.output.state ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output ∧
      record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨term,body,termStep,split,member,unsunk,branch,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope events block (by rw [ret]; rfl)
  have statement : b.body[front.length]? = some stm := by
    rw [shape,List.getElem?_append_right (Nat.le_refl _)]
    simp
  have defined : event.ctx.defInst? z = some (blockStart f event.block+front.length) :=
    stock_lower_source_result_definition run dominated events block statement (by simp [results])
  have safe := stock_lower_return_demand_unsunk run scope events block ret member
    split.termInst recorded emitted (by simp) defined
  have scanned := split.scanned
  simp only [sourceBodyIndices,shape,List.length_append,List.length_cons,List.length_nil,
    List.range_succ,List.map_append,List.map_cons,List.map_nil,List.reverse_append,
    List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] at scanned
  cases scanned with
  | cons head rest =>
    rename_i scan tail
    let record : ScanRecord := ⟨blockStart f event.block+front.length,term.output.state,scan⟩
    have current : record.inst = blockStart f event.block+front.length := rfl
    obtain ⟨info,source,clif,infoResults⟩ := ArithmeticBody.body_source_info run events split statement current
    have mandatory : event.ctx.insts[record.inst]!.clif.any mustLower = true := by
      simp only [getElem!_def,source,Option.getD_some,clif,division,Option.any,mustLower]
    have ordinary : record.inst ≠ event.termInst := by
      rw [current,split.termIndex,shape,List.length_append]
      simp only [List.length_cons,List.length_nil]
      omega
    obtain ⟨step,decision,actual⟩ := stock_mandatory_unsunk_emitted safe ordinary mandatory head
    exact ⟨term,record,_,step,split,List.mem_cons_self ..,rfl,rfl,head,
      split.retained record (List.mem_cons_self ..),decision,actual⟩
end Backend.Stock.Proof
#print axioms Backend.Stock.Proof.stock_lower_last_div_return_emitted
