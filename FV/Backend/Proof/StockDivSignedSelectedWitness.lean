import FV.Backend.Proof.StockDivSignedRecordReceipts
namespace Backend.Stock.Proof.ScalarDiv.SignedSelectedWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def Supported (ty : Clif.Ty) := ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64
private def function (safe : Bool) (ty : Clif.Ty) : Clif.Function := {
  name := "stock_sdiv_selected_record"
  sig := {
    params := (if safe then [⟨ty,.none,.normal⟩] else [⟨ty,.none,.normal⟩,⟨ty,.none,.normal⟩])
    returns := [⟨ty,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := (if safe then [(7,ty)] else [(7,ty),(31,ty)])
    body := (if safe then [⟨[31],.iconst ty (BitVec.ofNat ty.width 9)⟩] else []) ++
      [⟨[100],.div .sdiv ty 7 31⟩]
    term := .ret [100] }] }
private def expectedRule (safe : Bool) (ty : Clif.Ty) : Rule :=
  if safe then if ty.width = 64 then rule_lower_1163 else rule_lower_1167
  else if ty.width = 64 then rule_lower_1145 else rule_lower_1153
private def observed (safe : Bool) (ty : Clif.Ty) : Option Bool :=
  (Stock.lower (function safe ty)).toOption.map (fun result => result.blockScans.toList.any (fun event =>
    event.output.records.any (fun record =>
      (event.ctx.insts[record.inst]?).any (fun info => decide (info.clif = some (.div .sdiv ty 7 31))) &&
      record.output.step.any (fun step => step.decision == .emitted &&
        decide (step.rules.getLast? = some (expectedRule safe ty).id)))))
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed_run (safe : Bool) (ty : Clif.Ty) (supported : Supported ty) : observed safe ty = some true := by
  cases safe <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
end Kernel
/-- Eight actual complete driver runs inhabit all four general/safe signed
root selections and real retained bindings at8/16/32/64. Source machine
success/trap transfer remains a separate obligation. -/
theorem stock_div_sdiv_selected_record_witness (safe : Bool) (ty : Clif.Ty) (supported : Supported ty) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step)
      (info : IInfo) (receipt : RecordSelection event record step),
      Stock.lower (function safe ty) = .ok result ∧ LowerScope (function safe ty) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.div .sdiv ty 7 31) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (expectedRule safe ty).id ∧
      SignedSelectedReceipt event.ctx 7 31 ty.width (scanState record.input record.inst) receipt.next receipt.out := by
  have actual := observed_run safe ty supported
  unfold observed at actual
  cases run : Stock.lower (function safe ty) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq,List.any_eq_true,
      Bool.and_eq_true,Option.any_eq_true,decide_eq_true_eq,beq_iff_eq] at actual
    obtain ⟨event,events,record,records,⟨info,source,clif⟩,step,recorded,emitted,selected⟩ := actual
    have scope : LowerScope (function safe ty) := lowerScope_of
      (by cases safe <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel)
    obtain ⟨receipt,values⟩ := stock_lower_sdiv_record_receipt run scope events records source clif recorded emitted
    exact ⟨result,event,record,step,info,receipt,rfl,scope,events,records,source,clif,recorded,emitted,selected,values⟩
end Backend.Stock.Proof.ScalarDiv.SignedSelectedWitness
