namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem records_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- One original quiet statement derives its actual omission/emission and
result mapping even when other source statements are colored. -/
theorem actual_quiet_source_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {record : ScanRecord} (member : record ∈ body.records)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j)
    (quiet : colored stm.inst = false)
    (single : (stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig))
      (f.sigDecls.lookup ·)).map List.length = some 1) :
    PureBody.SourceRecord f event.ctx event.block record := by
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have bi : event.block = 0 := by simpa using bound
  have current' : record.inst = j := by simpa [bi,blockStart] using current
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have ordinary : record.inst ≠ event.termInst := by
    rw [current',split.termIndex,bi]
    simp only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add]
    omega
  have preserved := (stock_lower_quiet_single_block_unsunk run blocks statement quiet).2.2 event events
  have safe : record.input.sunk[record.inst]! = false := by
    rw [current']
    exact (preserved.2 record (split.retained record member)).1
  have actual := records_execute split.scanned record member
  obtain ⟨step,recorded,decision⟩ := stock_ordinary_unsunk_decision safe ordinary actual
  have decided : step.decision = .omitted ∨ step.decision = .emitted := by
    rcases decision with omitted | remembered | emitted
    · exact Or.inl omitted
    · exact False.elim ((Coverage.lower_record_noOpportunistic scope run events
        (split.retained record member) recorded) remembered)
    · exact Or.inr emitted
  refine ⟨j,b,stm,split.block,statement,current,step,recorded,?_⟩
  rcases decided with omitted | emitted
  · exact Or.inl omitted
  · obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
    have inv := (stock_lower_record_context run scope events).1
    obtain ⟨tys,types,typed,arity⟩ := inv.resTys record.inst info stm.inst source clif
    rw [types] at single
    have length : info.results.length = 1 := arity.trans (Option.some.inj single)
    obtain ⟨x,infoResults⟩ : ∃ x, info.results = [x] := by
      cases values : info.results with
      | nil => simp [values] at length
      | cons x rest =>
        cases rest with
        | nil => exact ⟨x,rfl⟩
        | cons y tail => simp [values] at length
    obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan actual recorded emitted
    have atInst : event.ctx.insts[record.inst]! = info := by
      simp only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,source,Option.getD_some]
    obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun
      (by rw [atInst]; exact infoResults)
    obtain ⟨a,rfl⟩ := inv.valueReg x r mapped
    exact Or.inr ⟨emitted,info,x,a,source,clif,infoResults,results.symm.trans infoResults,mapped⟩
end Backend.Stock.Proof.QuietSourceColors
#print axioms Backend.Stock.Proof.QuietSourceColors.actual_quiet_source_record
