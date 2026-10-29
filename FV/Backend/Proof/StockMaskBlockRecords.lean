module

public import FV.Backend.Proof.StockQuietBlockSourceRecords
public import FV.Backend.Proof.StockMaskBodyRecords

@[expose] public section

namespace Backend.Stock.Proof.MaskBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

private theorem records_execute {exec : Nat → State → Except String Scan}
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

/-- Quiet zero-result source instructions, including nop, are omitted by the
actual whole-driver scan even when other body positions have effect colors. -/
theorem actual_nop_record_at_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block}
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {record : ScanRecord} (member : record ∈ body.records)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j) (nop : stm.inst = .nop) :
    ∃ step,record.output.step = some step ∧ step.decision = .omitted := by
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have ordinary : record.inst ≠ event.termInst := by
    rw [current,split.termIndex]; omega
  have preserved := (QuietSourceColors.stock_lower_quiet_block_unsunk run split.block statement
    (by rw [nop]; rfl)).2.2 event events
  have safe : record.input.sunk[record.inst]! = false := by
    rw [current]
    exact (preserved.2 record (split.retained record member)).1
  obtain ⟨info,source,clif,_⟩ := ArithmeticBody.body_source_info run events split statement current
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨tys,computed,typed,arity⟩ := inv.resTys record.inst info stm.inst source clif
  have emptyTypes : tys = [] := by simpa only [nop,Clif.Inst.resultTypes,Option.some.injEq] using computed.symm
  have empty : info.results = [] := List.length_eq_zero_iff.mp (by simpa only [emptyTypes,List.length_nil] using arity)
  have bang : event.ctx.insts[record.inst]! = info := by simp only [getElem!_def,source]
  have expected := scan_zero_results (ctx := event.ctx) (block := event.block) (isBranch := event.isBranch)
    safe ordinary (by rw [bang]; exact empty)
    (by rw [bang,clif,nop]; rfl)
  have actual := records_execute split.scanned record member
  have equal := Except.ok.inj (actual.symm.trans expected)
  exact ⟨_,by rw [equal],rfl⟩


/-- The real scan and source syntax derive every record class for arbitrary
interleavings, retaining old division behavior, bmask binding and zero-result nop. -/
theorem actual_families_at_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,Family stm.inst)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b) :
    ∃ term body,SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records,Record f event.ctx event.block record := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have same : original = b := Option.some.inj (split.block.symm.trans block)
  subst original
  have sourceFormats : ∀ b' ∈ f.blocks,∀ stm ∈ b'.body,CastComplete.MemoryFormat stm.inst := by
    intro b' member stm present
    exact family_formats (family b' member stm present)
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  obtain ⟨info,source,clif,_⟩ := ArithmeticBody.body_source_info run events split statement current
  rcases family b (List.mem_of_getElem? block) stm (List.mem_of_getElem? statement) with (scalar | ⟨op,ty,x,y,division⟩) | ⟨ty,x,mask⟩ | nop
  · exact .old (.scalar split.block statement current source clif scalar
      (QuietSourceColors.actual_quiet_source_record_at_block run scope events split member statement current
        (HighMulBody.family_quiet scalar) (HighMulBody.family_single scalar f)))
  · exact .old (DivBody.actual_division_record run scope sourceFormats events split member statement current division)
  · exact .bmask split.block statement current mask source (clif.trans (congrArg some mask))
      (QuietSourceColors.actual_quiet_source_record_at_block run scope events split member statement current
        (by rw [mask]; rfl) (by rw [mask]; rfl))
  · obtain ⟨step,recorded,omitted⟩ := actual_nop_record_at_block run scope events split member statement current nop
    exact .nop split.block statement current source (clif.trans (congrArg some nop)) recorded omitted

end Backend.Stock.Proof.MaskBody
