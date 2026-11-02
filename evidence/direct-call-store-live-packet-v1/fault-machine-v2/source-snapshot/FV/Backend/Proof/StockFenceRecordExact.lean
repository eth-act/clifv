import FV.Backend.Proof.StockFenceRecord
import FV.Backend.Proof.StockFenceSelected

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem scan_empty (st : State) (i : Nat) :
    (scanState st i).base.emitted = #[] := by
  unfold scanState
  dsimp only
  split <;> rfl

/-- Every actual source fence has an emitted record with no results or copies.
The proof derives the root, binding and complete scheduling frame internally. -/
theorem stock_lower_fence_record_exact {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} (found : event.ctx.insts[record.inst]? = some info)
    (source : info.clif = some .fence) :
    ∃ step, record.output.step = some step ∧ step.decision = .emitted ∧
      step.results = [] ∧ step.rules.getLast? = some 1024 ∧
      record.output.emitted = #[.fence] ∧
      record.output.state = {scanState record.input record.inst with
        base := (scanState record.input record.inst).base.emit .fence} := by
  obtain ⟨emission,call,scan⟩ := stock_lower_fence_emission run scope events records found source
  let step : Step := ⟨event.block,record.inst,.emitted,scanState record.input record.inst,
    emission.state,emission.results,emission.rules,emission.code⟩
  have recorded : record.output.step = some step := by rw [scan]; rfl
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded rfl
  have context := (stock_lower_record_context run scope events).1
  have selected := stock_fence_selected_exact context found source receipt.selected
  have results : receipt.results = [] := V.regsVec.inj (receipt.output.symm.trans selected.1)
  have empty := SinkRules.fence_results_empty context found source
  have binding := receipt.binding
  rw [empty] at binding
  change Except.ok (receipt.next,#[]) = Except.ok (receipt.bound,receipt.copies) at binding
  have state : receipt.bound = receipt.next := (congrArg Prod.fst (Except.ok.inj binding)).symm
  have copies : receipt.copies = #[] := (congrArg Prod.snd (Except.ok.inj binding)).symm
  refine ⟨step,recorded,rfl,receipt.resultRegs.trans results,receipt.rules ▸ selected.2.2,?_,?_⟩
  · rw [receipt.code,copies,state,selected.2.1]
    simp only [LState.emit,scan_empty,Array.append_empty]
    rfl
  · exact receipt.state.trans (state.trans selected.2.1)

end Backend.Stock.Proof
