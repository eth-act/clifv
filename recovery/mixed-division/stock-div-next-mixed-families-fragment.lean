namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The real single-block event selects the source block, independently of
its instruction families and source outcomes. -/
private theorem mixed_event_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    f.blocks[event.block]? = some b := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have zero : event.block = 0 := by simpa using bound
  simp [zero,blocks]

/-- Derive every mixed body's actual record from its source syntax and real
whole-driver run. The final division's retention comes from return demand;
every pure prefix position derives quietness and its own concrete decision. -/
theorem actual_mixed_div_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records,MixedDivRecord f event.ctx event.block record := by
  have block := mixed_event_block run scope blocks events
  obtain ⟨term,last,body,step,info,a,split,lastMember,lastIndex,lastInput,
    lastRetained,lastStep,lastEmitted,lastSource,lastClif,lastResults,lastMapped⟩ :=
      actual_last_div_record run scope dominated events block shape division results ret
  have lastStatement : b.body[front.length]? = some stm := by
    rw [shape,List.getElem?_append_right (Nat.le_refl _)]; simp
  have unique : (sourceBodyIndices f event.block b).Nodup := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b different eq => different (Nat.add_left_cancel eq.symm)) List.nodup_range
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,item,statement,current⟩ := split.positions record member
  by_cases final : j = front.length
  · subst j
    have same : record = last := split.scanned.record_unique unique member lastMember
      (current.trans lastIndex.symm)
    subst record
    have sameItem : item = stm := Option.some.inj (statement.symm.trans lastStatement)
    subst item
    exact .division block lastStatement lastIndex lastSource lastClif lastResults results
      lastMapped lastStep lastEmitted
  · have inside := (List.getElem?_eq_some_iff.mp statement).1
    have before : j < front.length := by
      rw [shape,List.length_append] at inside
      simp only [List.length_cons,List.length_nil] at inside
      omega
    have original : front[j]? = some item := by
      rw [shape,List.getElem?_append_left before] at statement
      exact statement
    have itemFamily := family item (List.mem_of_getElem? original)
    have described := QuietSourceColors.actual_quiet_source_record run scope blocks events split
      member statement current (HighMulBody.family_quiet itemFamily)
      (HighMulBody.family_single itemFamily f)
    obtain ⟨sourceInfo,source,clif,sourceResults⟩ := ArithmeticBody.body_source_info run events split statement current
    exact .scalar block statement current source clif itemFamily described

end Backend.Stock.Proof.DivBody
#print axioms Backend.Stock.Proof.DivBody.actual_mixed_div_families
