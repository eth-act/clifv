import FV.Backend.Proof.StockProtectedSinkDriver
import FV.Backend.Proof.StockStoreMixedRetention
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.SinkRules.ProtectedDriverWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

private def function : Clif.Function := {
  name := "mixed_memory_protected_driver"
  sig := {params := List.replicate 2 ⟨.i64,.none,.normal⟩,returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(0,.i64),(1,.i64)],body := [
    ⟨[2],.load .load .i8 {} 0 0⟩,
    ⟨[3],.extend .uextend .i64 2⟩,
    ⟨[],.store .store .i64 {} 1 0 0⟩],term := .ret [3]}] }
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private def observed : Bool :=
  match Stock.lower function with
  | .ok result => match result.ctx.insts[2]? with
    | some info => decide (info.clif = some (.store .store .i64 {} 1 0 0)) &&
      result.final.sunk[0]! && !result.final.sunk[2]! &&
      result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
        record.inst == 2 && record.output.step.any (fun step => step.decision == .emitted)))
    | none => false
  | _ => false
private theorem observed_true : observed = true := by native_decide

/-- Complete original Stock lowering sinks the load and emits the protected store.
The generic whole-driver theorem supplies every actual retained boundary. -/
theorem complete_driver_witness :
    ∃ result info,LowerScope function ∧ Stock.lower function = .ok result ∧
      result.ctx.insts[2]? = some info ∧ info.clif = some (.store .store .i64 {} 1 0 0) ∧
      result.final.sunk[0]! = true ∧ result.final.sunk[2]! = false ∧
      (∃ event ∈ result.blockScans.toList,∃ record ∈ event.output.records,
        record.inst = 2 ∧ ∃ step,record.output.step = some step ∧ step.decision = .emitted) ∧
      ∀ event ∈ result.blockScans.toList,event.input.sunk[2]! = false ∧
        ∀ record ∈ event.output.records,record.input.sunk[2]! = false ∧
          record.output.state.sunk[2]! = false := by
  have h := observed_true
  unfold observed at h
  split at h
  · rename_i result run
    split at h
    · rename_i info found
      have checked : info.clif = some (.store .store .i64 {} 1 0 0) ∧
          result.final.sunk[0]! = true ∧ (!result.final.sunk[2]!) = true ∧
          result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
            record.inst == 2 && record.output.step.any (fun step => step.decision == .emitted))) = true := by
        simpa only [Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
      have frames := stock_lower_store_unsunk run scope found checked.1
      refine ⟨result,info,scope,run,found,checked.1,checked.2.1,frames.1,?_,frames.2⟩
      obtain ⟨event,member,emitted⟩ := List.any_eq_true.mp checked.2.2.2
      obtain ⟨record,retained,test⟩ := List.any_eq_true.mp emitted
      have both : record.inst = 2 ∧
          record.output.step.any (fun step => step.decision == .emitted) = true := by
        simpa only [Bool.and_eq_true,beq_iff_eq] using test
      cases foundStep : record.output.step with
      | none => simp [foundStep] at both
      | some step =>
        exact ⟨event,member,record,retained,both.1,step,foundStep,by simpa [foundStep] using both.2⟩
    · cases h
  · cases h

/-- A real mixed function inhabits source-indexed store retention and emission. -/
theorem complete_store_retention_witness :
    ∃ result event b term record body step,
      LowerScope function ∧ Stock.lower function = .ok result ∧
      event ∈ result.blockScans.toList ∧ function.blocks[event.block]? = some b ∧
      b.body[2]? = some ⟨[],.store .store .i64 {} 1 0 0⟩ ∧
      SourceBodySplit function event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart function event.block+2 ∧
      record.input.sunk[record.inst]! = false ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨result,info,scopedInput,run,found,source,load,store,emitted,frames⟩ := complete_driver_witness
  obtain ⟨event,member,_⟩ := emitted
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scopedInput member
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  have eventZero : event.block = 0 := by change event.block < 1 at bound; omega
  have block : function.blocks[event.block]? = some function.blocks[0]! := by rw [eventZero]; rfl
  have statement : function.blocks[0]!.body[2]? = some ⟨[],.store .store .i64 {} 1 0 0⟩ := rfl
  obtain ⟨term,record,body,step,parts,retained,index,unsunk,actual,recorded,decision,emits⟩ :=
    stock_lower_mixed_store_emitted run scopedInput member block statement
  exact ⟨result,event,function.blocks[0]!,term,record,body,step,scopedInput,run,member,block,
    statement,parts,retained,index,unsunk,actual,recorded,decision,emits⟩

end Backend.Stock.Proof.SinkRules.ProtectedDriverWitness
