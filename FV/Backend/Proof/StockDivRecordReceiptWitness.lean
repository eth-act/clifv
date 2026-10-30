import FV.Backend.Proof.StockDivSelectedWitness
import FV.Backend.Proof.StockDivRemSelectedWitness
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
/-- The actual retained unsigned fixtures inhabit every original premise of
the whole-driver record receipt, including source scope and real binding. -/
theorem stock_div_udiv_record_receipt_witness (ty : Clif.Ty)
    (width : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord)
      (step : Step) (info : IInfo) (receipt : RecordSelection event record step),
      Stock.lower f = .ok result ∧ LowerScope f ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.div .udiv ty 7 31) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      (if ty.width = 64 then WideUdivReceipt program event.ctx 999949 7 31
        (scanState record.input record.inst) receipt.next #[] receipt.out
       else NarrowUdivReceipt program event.ctx 999949 7 31 ty.width
        (scanState record.input record.inst) receipt.next #[] receipt.out) := by
  obtain ⟨result,event,record,step,info,receipt,run,events,records,source,clif,recorded,emitted,values⟩ :=
    SelectedWitness.stock_div_udiv_selected_record_witness ty width
  refine ⟨_,result,event,record,step,info,receipt,run,?_,events,records,source,clif,recorded,emitted,values⟩
  exact lowerScope_of (by rcases width with rfl | rfl | rfl | rfl <;> decide +kernel)
/-- Both retained remainder fixtures inhabit all original source-scope and
binding premises across8/16/32/64. -/
theorem stock_div_rem_record_receipt_witness (signed : Bool) (ty : Clif.Ty)
    (width : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord)
      (step : Step) (info : IInfo) (receipt : RecordSelection event record step),
      Stock.lower f = .ok result ∧ LowerScope f ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.div (if signed then .srem else .urem) ty 7 31) ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      (if ty.width = 64 then WideRemReceipt program event.ctx signed 999899 7 31
        (scanState record.input record.inst) receipt.next #[] receipt.out
       else NarrowRemReceipt program event.ctx signed 999899 7 31 ty.width
        (scanState record.input record.inst) receipt.next #[] receipt.out) := by
  obtain ⟨result,event,record,step,info,receipt,run,events,records,source,clif,recorded,emitted,values⟩ :=
    RemSelectedWitness.stock_div_rem_selected_record_witness signed ty width
  refine ⟨_,result,event,record,step,info,receipt,run,?_,events,records,source,clif,recorded,emitted,values⟩
  exact lowerScope_of (by cases signed <;> rcases width with rfl | rfl | rfl | rfl <;> decide +kernel)
end Backend.Stock.Proof.ScalarDiv
