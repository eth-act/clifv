import FV.Backend.Proof.StockProtectedSinkScan
import FV.Backend.Proof.StockProtectedSinkSource
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.SinkRules.ProtectedScanWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm scanBlock scanInstruction

private def function : Clif.Function := {
  name := "mixed_memory_protected_scan"
  sig := {params := List.replicate 2 ⟨.i64,.none,.normal⟩,returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(0,.i64),(1,.i64)],body := [
    ⟨[2],.load .load .i8 {} 0 0⟩,
    ⟨[3],.extend .uextend .i64 2⟩,
    ⟨[],.store .store .i64 {} 1 0 0⟩],term := .ret [3]}] }
private def built := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def input := built.2.2.mark 3
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem mapped : MappedCtxInv function built.1 :=
  buildCtx_mappedInv scope (ranges := built.2.1) (st := built.2.2) rfl
private theorem safe : NoLoadAt built.1 2 := store_no_load_at mapped (slot := 2) rfl rfl
private theorem empty : built.1.insts[2]!.results = [] := store_results_empty mapped (slot := 2) rfl rfl

private def observed : Bool :=
  match scanBlock built.1 0 3 false [2,1,0] input with
  | .ok output => output.state.sunk[0]! && !output.state.sunk[2]! &&
    output.records.any (fun record => record.inst == 2 &&
      record.output.step.any (fun step => step.decision == .emitted))
  | _ => false
private theorem observed_true : observed = true := by native_decide

/-- A complete actual scan sinks a load, emits a store and preserves every store boundary. -/
theorem complete_scan_witness :
    ∃ output,LowerScope function ∧ MappedCtxInv function built.1 ∧
      NoLoadAt built.1 2 ∧ built.1.insts[2]!.results = [] ∧
      2 < input.sunk.size ∧ input.sunk[2]! = false ∧
      scanBlock built.1 0 3 false [2,1,0] input = .ok output ∧
      output.state.sunk[0]! = true ∧ output.state.sunk[2]! = input.sunk[2]! ∧
      (∃ record ∈ output.records,record.inst = 2 ∧
        ∃ step,record.output.step = some step ∧ step.decision = .emitted) ∧
      ∀ record ∈ output.records,record.input.sunk[2]! = input.sunk[2]! ∧
        record.output.state.sunk[2]! = input.sunk[2]! := by
  have h := observed_true
  unfold observed at h
  split at h
  · rename_i output run
    have facts := scan_block_protected_slot mapped safe empty run
    have checked : output.state.sunk[0]! = true ∧ (!output.state.sunk[2]!) = true ∧
        output.records.any (fun record => record.inst == 2 &&
          record.output.step.any (fun step => step.decision == .emitted)) = true := by
      simpa only [Bool.and_eq_true,and_assoc] using h
    refine ⟨output,scope,mapped,safe,empty,by decide,rfl,run,checked.1,facts.1,?_,facts.2⟩
    obtain ⟨record,member,test⟩ := List.any_eq_true.mp checked.2.2
    have both : record.inst = 2 ∧
        record.output.step.any (fun step => step.decision == .emitted) = true := by
      simpa only [Bool.and_eq_true,beq_iff_eq] using test
    cases found : record.output.step with
    | none => simp [found] at both
    | some step =>
      exact ⟨record,member,both.1,step,found,by simpa [found] using both.2⟩
  · cases h

end Backend.Stock.Proof.SinkRules.ProtectedScanWitness
