import FV.Backend.Proof.StockControlShape
import FV.Backend.Proof.StockReturnRecordCalls
import FV.Backend.Proof.StockTerminalEmission

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver

/-- Every actual original return scan ends in the actual ABI return, following
its complete ordinary body. Neither a selected rule nor terminal-record code is
supplied as a premise. -/
theorem stock_lower_return_scan_last {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b) {xs : List Nat}
    (ret : b.term = .ret xs) :
    ∃ (rs ps : List Reg),event.output.code.back? = some (.rets (rs.zip ps)) ∧
      returnPins f rs.length = some ps := by
  obtain ⟨record,body,step,split,records,_,_,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope events block (by rw [ret]; rfl)
  obtain ⟨fuel,trace,rs,ps,_,_,_,_,pins,_,code⟩ :=
    stock_lower_return_record_helper run scope events block ret records split.termInst recorded emitted
  refine ⟨rs,ps,?_,pins⟩
  rw [split.code,code,Array.back?_append]
  rfl

/-- Every actual original trap scan ends in the original coded UDF, after
its ordinary body. Mandatory emission, root selection and the empty binder
are derived from the whole Stock lowering run. -/
theorem stock_lower_trap_scan_last {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b) {c : Clif.TrapCode}
    (trap : b.term = .trap c) : event.output.code.back? = some (.udf c) := by
  obtain ⟨record,body,step,split,records,_,_,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope events block (by rw [trap]; rfl)
  obtain ⟨original,data,found,prepared,slot⟩ := stock_lower_blockScan_term_data run scope events
  have same := Option.some.inj (found.symm.trans block)
  subst original
  rw [trap] at prepared
  change Backend.termData (.trap c) = .ok data at prepared
  rw [termData_trap] at prepared
  cases prepared
  rw [← split.termInst] at slot
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  obtain ⟨state,_,_⟩ := Control.stock_named_trap_shape slot receipt.rootRun
  have binding := receipt.binding
  simp only [getElem!_def,slot,List.zip_nil_left] at binding
  change Except.ok (receipt.next,#[]) = Except.ok (receipt.bound,receipt.copies) at binding
  obtain ⟨boundEq,copiesEq⟩ := Prod.mk.inj (Except.ok.inj binding)
  have empty : (scanState record.input record.inst).base.emitted = #[] := by
    unfold scanState
    dsimp only
    split <;> rfl
  have code : record.output.emitted = #[.udf c] := by
    rw [receipt.code,← boundEq,← copiesEq,state]
    simp only [LState.emit,empty,Array.append_empty]
    rfl
  rw [split.code,code,Array.back?_append]
  rfl

end Backend.Stock.Proof
