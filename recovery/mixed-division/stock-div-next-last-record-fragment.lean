namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 8192

/-- Extract the final division's actual retained record, result binding and
mapped virtual destination after an arbitrary original source prefix. -/
theorem actual_last_div_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z]) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step) (info : IInfo) (a : Nat),
      SourceBodySplit f event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart f event.block+front.length ∧ record.input = term.output.state ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.div op ty x y) ∧
      info.results = [z] ∧ event.ctx.valueReg? z = some (.vreg a .int) := by
  obtain ⟨term,record,body,step,split,bodyMember,current,input,scan,member,recorded,emitted⟩ :=
    stock_lower_last_div_return_emitted run scope dominated events block shape division results ret
  have statement : b.body[front.length]? = some stm := by
    rw [shape,List.getElem?_append_right (Nat.le_refl _)]; simp
  obtain ⟨info,source,clif,infoResults⟩ := ArithmeticBody.body_source_info run events split statement current
  obtain ⟨emission,emissionRun,scanEq⟩ := stock_emitted_scan scan recorded emitted
  obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped (z := z) emissionRun
    (by simp only [getElem!_def,source,Option.getD_some,infoResults,results])
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
  exact ⟨term,record,body,step,info,a,split,bodyMember,current,input,member,recorded,emitted,
    source,clif.trans (congrArg some division),infoResults.trans results,mapped⟩
end Backend.Stock.Proof.DivBody
#print axioms Backend.Stock.Proof.DivBody.actual_last_div_record
