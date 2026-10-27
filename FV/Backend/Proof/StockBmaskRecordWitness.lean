import FV.Backend.Proof.StockBmaskRecord
import FV.Backend.Proof.StockBmaskSelectionWitness

namespace Backend.Stock.Proof.ScalarMask
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed_record :
    (Stock.lower bmaskWitnessFunction).toOption.map (fun result =>
      result.blockScans.toList.any (fun event => event.output.records.any (fun record =>
        record.inst == 0 &&
        ((event.ctx.insts[record.inst]?).any (fun info =>
          decide (info.clif = some (.bmask .i8 7)) && decide (info.results = [100])) &&
        (decide (event.ctx.valueReg? 100 = some (.vreg 193 .int)) &&
        (decide (event.ctx.valueType? 7 = some (.int 64)) &&
        (decide (event.ctx.valueReg? 7 = some (.vreg 192 .int)) &&
        (decide (event.ctx.defInst? 7 = none) &&
        record.output.step.any (fun step => step.decision == .emitted))))))))) = some true := by
  decide +kernel
end Kernel

/-- A complete successful Stock driver run inhabits retained bmask selection,
result binding and exact code/state, including the original source record. -/
theorem stock_lower_bmask_record_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (info : IInfo)
      (step : Step) (wi nx : Nat) (next : State),
      Stock.lower bmaskWitnessFunction = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.bmask .i8 7) ∧
      info.results = [100] ∧ event.ctx.valueReg? 100 = some (.vreg 193 .int) ∧
      event.ctx.valueType? 7 = some (.int 64) ∧ event.ctx.valueReg? 7 = some (.vreg 192 .int) ∧
      event.ctx.defInst? 7 = none ∧ record.inst = 0 ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.results = [[.vreg (bmaskResultNum wi record.input.base.nextVreg) .int]] ∧
      next = {(scanState record.input record.inst).mark 7 with
        base := bmaskBase (scanState record.input record.inst).base wi (.vreg nx .int)} ∧
      record.output.state = {next with alias := aliasStep next.alias (193,bmaskResultNum wi record.input.base.nextVreg)} ∧
      record.output.emitted.toList = bmaskCode wi record.input.base.nextVreg nx ∧
      record.output.state.base.nextVreg = record.input.base.nextVreg+bmaskAlloc wi := by
  have success := observed_record
  cases run : Stock.lower bmaskWitnessFunction with
  | error err => simp only [run,Except.toOption,Option.map_none] at success; cases success
  | ok result =>
    rw [run] at success
    simp only [Except.toOption,Option.map_some,Option.some.injEq,List.any_eq_true] at success
    obtain ⟨event,events,found⟩ := success
    simp only [Array.any_eq_true,Bool.and_eq_true,beq_iff_eq,Option.any_eq_true,decide_eq_true_eq] at found
    obtain ⟨record,records,current,⟨info,source,clif,results⟩,mapped,typed,mapX,undefined,step,recorded,emitted⟩ := found
    have scope : LowerScope bmaskWitnessFunction := lowerScope_of (by decide +kernel)
    obtain ⟨wi,nx,next,_,_,_,_,output,nextEq,stateEq,code,frontier⟩ :=
      stock_lower_bmask_record run scope events records source clif results mapped recorded emitted
    exact ⟨result,event,record,info,step,wi,nx,next,rfl,events,records,source,clif,results,mapped,typed,mapX,undefined,current,
      recorded,emitted,output,nextEq,stateEq,code,frontier⟩

end Backend.Stock.Proof.ScalarMask
