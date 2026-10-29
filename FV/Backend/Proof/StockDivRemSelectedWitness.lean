module

public import FV.Backend.Proof.StockDivSelected

@[expose] public section

namespace Backend.Stock.Proof.ScalarDiv.RemSelectedWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def Supported (ty : Clif.Ty) := ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64
private def function (signed : Bool) (ty : Clif.Ty) : Clif.Function := {
  name := "stock_rem_selected_record"
  sig := {params := [⟨ty,.none,.normal⟩,⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty),(31,ty)],body := [⟨[100],.div (if signed then .srem else .urem) ty 7 31⟩],term := .ret [100]}] }
private def observed (signed : Bool) (ty : Clif.Ty) : Option Bool :=
  (Stock.lower (function signed ty)).toOption.map (fun result => result.blockScans.toList.any (fun event =>
    event.output.records.any (fun record =>
      (event.ctx.insts[record.inst]?).any (fun info => decide (info.clif = some (.div (if signed then .srem else .urem) ty 7 31))) &&
      record.output.step.any (fun step => step.decision == .emitted))))
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed_run (signed : Bool) (ty : Clif.Ty) (supported : Supported ty) : observed signed ty = some true := by
  cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
end Kernel
/-- Eight actual whole-driver runs supply retained signed/unsigned remainder records,
real result binding and the internally derived selected RHS receipt. This is
an actual retained-selection witness; source machine simulation remains separate. -/
theorem stock_div_rem_selected_record_witness (signed : Bool) (ty : Clif.Ty) (supported : Supported ty) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step)
      (info : IInfo) (receipt : RecordSelection event record step),
      Stock.lower (function signed ty) = .ok result ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ event.ctx.insts[record.inst]? = some info ∧
      info.clif = some (.div (if signed then .srem else .urem) ty 7 31) ∧ record.output.step = some step ∧ step.decision = .emitted ∧
      (if ty.width = 64 then WideRemReceipt program event.ctx signed 999899 7 31
        (scanState record.input record.inst) receipt.next #[] receipt.out
       else NarrowRemReceipt program event.ctx signed 999899 7 31 ty.width
        (scanState record.input record.inst) receipt.next #[] receipt.out) := by
  have actual := observed_run signed ty supported
  unfold observed at actual
  cases run : Stock.lower (function signed ty) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq,List.any_eq_true,
      Bool.and_eq_true,Option.any_eq_true,decide_eq_true_eq,beq_iff_eq] at actual
    obtain ⟨event,events,record,records,⟨info,source,clif⟩,step,recorded,emitted⟩ := actual
    have scope : LowerScope (function signed ty) := lowerScope_of
      (by cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel)
    obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
    have inv := (stock_lower_record_context run scope events).1
    exact ⟨result,event,record,step,info,receipt,rfl,events,records,source,clif,recorded,emitted,
      stock_div_rem_selected inv signed source clif receipt.selected⟩
end Backend.Stock.Proof.ScalarDiv.RemSelectedWitness
