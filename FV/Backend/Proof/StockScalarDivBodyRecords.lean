import FV.Backend.Proof.StockNoLoadDriver
import FV.Backend.Proof.StockMixedDivBodyRefines

namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

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

/-- Actual source/driver execution derives emission and result binding for a
division at any retained position, whether its result is used or returned. -/
theorem actual_division_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (formats : ∀ b ∈ f.blocks, ∀ stm ∈ b.body, CastComplete.MemoryFormat stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    {record : ScanRecord} (member : record ∈ body.records)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat}
    (division : stm.inst = .div op ty x y) : MixedDivRecord f event.ctx event.block record := by
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
  have safe := ((SinkRules.stock_lower_no_load_unsunk run scope formats record.inst).2
    event events).2 record (split.retained record member)
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have ordinary : record.inst ≠ event.termInst := by rw [current,split.termIndex]; omega
  have mandatory : event.ctx.insts[record.inst]!.clif.any mustLower = true := by
    simp only [getElem!_def,source,Option.getD_some,clif,division,Option.any,mustLower]
  have actual := records_execute split.scanned record member
  obtain ⟨step,recorded,emitted⟩ := stock_mandatory_unsunk_emitted safe.1 ordinary mandatory actual
  have inv := (stock_lower_record_context run scope events).1
  have original : info.clif = some (.div op ty x y) := clif.trans (congrArg some division)
  obtain ⟨tys,computed,typed,arity⟩ := inv.resTys record.inst info _ source original
  have types : tys = [ty] := by simpa [Clif.Inst.resultTypes] using computed.symm
  rw [types] at arity
  obtain ⟨z,one⟩ : ∃ z,info.results = [z] := by
    cases values : info.results with
    | nil => simp [values] at arity
    | cons z rest =>
      cases rest with
      | nil => exact ⟨z,rfl⟩
      | cons a tail => simp [values] at arity
  obtain ⟨emission,emissionRun,scanEq⟩ := stock_emitted_scan actual recorded emitted
  obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped (z := z) emissionRun
    (by simp only [getElem!_def,source,Option.getD_some,one])
  obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
  exact MixedDivRecord.division split.block statement current source original one
    (results.symm.trans one) mapped recorded emitted

/-- Shared scalar/division source classification permits arbitrary ordering,
multiple divisions, unused results and divisions consumed by other statements. -/
theorem actual_scalar_div_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body,
      HighMulBody.Family stm.inst ∨ ∃ op ty x y,stm.inst = .div op ty x y)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records,MixedDivRecord f event.ctx event.block record := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have same : original = b := by
    have member := List.mem_of_getElem? split.block
    simpa only [blocks,List.mem_singleton] using member
  subst original
  have formats : ∀ b' ∈ f.blocks, ∀ stm ∈ b'.body,CastComplete.MemoryFormat stm.inst := by
    intro b' member stm statement
    have same : b' = b := by simpa only [blocks,List.mem_singleton] using member
    subst b'
    exact SinkRules.scalar_div_formats (family stm statement)
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  rcases family stm (List.mem_of_getElem? statement) with scalar | ⟨op,ty,x,y,division⟩
  · obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
    exact MixedDivRecord.scalar split.block statement current source clif scalar
      (QuietSourceColors.actual_quiet_source_record run scope blocks events split member statement current
        (HighMulBody.family_quiet scalar) (HighMulBody.family_single scalar f))
  · exact actual_division_record run scope formats events split member statement current division

end Backend.Stock.Proof.DivBody
