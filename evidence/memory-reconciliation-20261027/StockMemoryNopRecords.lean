import FV.Backend.Proof.StockMaskBodyRecords
import FV.Backend.Proof.StockQuietBlockSourceRecords

/-! UNVALIDATED next-source draft, excluded from the frozen production packet.
Generalize existing nop retention to arbitrary original blocks, including the
actual two-block/nop memory input. Old theorem variants remain untouched. -/
namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

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

theorem actual_nop_record_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block}
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {record : ScanRecord} (member : record ∈ body.records)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j) (nop : stm.inst = .nop) :
    ∃ step,record.output.step = some step ∧ step.decision = .omitted := by
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


end Backend.Stock.Memory
