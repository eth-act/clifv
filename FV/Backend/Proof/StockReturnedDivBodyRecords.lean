module

public import FV.Backend.Proof.StockReturnedDefinitionRetention
public import FV.Backend.Proof.StockMixedDivBodyRefines

@[expose] public section

namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

/-- Extract actual result binding for a returned division at any source slot.
All retention and mapped integer-destination facts come from the real driver. -/
theorem actual_returned_div_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z]) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step) (info : IInfo) (a : Nat),
      SourceBodySplit f event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart f event.block+j ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.div op ty x y) ∧
      info.results = [z] ∧ event.ctx.valueReg? z = some (.vreg a .int) := by
  obtain ⟨term,record,body,step,split,bodyMember,current,safe,scan,member,recorded,emitted⟩ :=
    stock_lower_returned_div_emitted run scope dominated events block statement division results ret
  obtain ⟨info,source,clif,infoResults⟩ := ArithmeticBody.body_source_info run events split statement current
  obtain ⟨emission,emissionRun,scanEq⟩ := stock_emitted_scan scan recorded emitted
  obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped (z := z) emissionRun
    (by simp only [getElem!_def,source,Option.getD_some,infoResults,results])
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
  exact ⟨term,record,body,step,info,a,split,bodyMember,current,member,recorded,emitted,
    source,clif.trans (congrArg some division),infoResults.trans results,mapped⟩

private theorem event_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {b : Clif.Block} (blocks : f.blocks = [b])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    f.blocks[event.block]? = some b := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have zero : event.block = 0 := by simpa using bound
  simp [zero,blocks]

/-- All source positions other than the distinguished division retain the
previously proved scalar family, before and after the division alike. -/
private theorem other_family {b : Clif.Block} {front back : List Clif.Stmt} {stm : Clif.Stmt}
    (shape : b.body = front ++ stm :: back)
    (before : ∀ item ∈ front,HighMulBody.Family item.inst)
    (after : ∀ item ∈ back,HighMulBody.Family item.inst)
    {j : Nat} {item : Clif.Stmt} (statement : b.body[j]? = some item)
    (different : j ≠ front.length) : HighMulBody.Family item.inst := by
  by_cases earlier : j < front.length
  · rw [shape,List.getElem?_append_left earlier] at statement
    exact before item (List.mem_of_getElem? statement)
  · have offset : j-front.length = (j-front.length-1)+1 := by omega
    rw [shape,List.getElem?_append_right (Nat.le_of_not_lt earlier),offset,
      List.getElem?_cons_succ] at statement
    exact after item (List.mem_of_getElem? statement)

/-- Every actual retained body record is either a proved scalar record or
the returned division, with no restriction that division is the last statement. -/
theorem actual_returned_div_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front back : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ stm :: back)
    (before : ∀ item ∈ front,HighMulBody.Family item.inst)
    (after : ∀ item ∈ back,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records,MixedDivRecord f event.ctx event.block record := by
  have block := event_block run scope blocks events
  have divisionAt : b.body[front.length]? = some stm := by
    rw [shape,List.getElem?_append_right (Nat.le_refl _)]; simp
  obtain ⟨term,chosen,body,step,info,a,split,chosenMember,chosenIndex,chosenRetained,
      chosenStep,chosenEmitted,chosenSource,chosenClif,chosenResults,chosenMapped⟩ :=
    actual_returned_div_record run scope dominated events block divisionAt division results ret
  have unique : (sourceBodyIndices f event.block b).Nodup := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b different eq => different (Nat.add_left_cancel eq.symm)) List.nodup_range
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,item,statement,current⟩ := split.positions record member
  by_cases selected : j = front.length
  · subst j
    have same : record = chosen := split.scanned.record_unique unique member chosenMember
      (current.trans chosenIndex.symm)
    subst record
    have sameItem : item = stm := Option.some.inj (statement.symm.trans divisionAt)
    subst item
    exact .division block divisionAt chosenIndex chosenSource chosenClif chosenResults results
      chosenMapped chosenStep chosenEmitted
  · have family := other_family shape before after statement selected
    have actual := QuietSourceColors.actual_quiet_source_record run scope blocks events split
      member statement current (HighMulBody.family_quiet family) (HighMulBody.family_single family f)
    obtain ⟨sourceInfo,source,clif,sourceResults⟩ :=
      ArithmeticBody.body_source_info run events split statement current
    exact .scalar block statement current source clif family actual

end Backend.Stock.Proof.DivBody
