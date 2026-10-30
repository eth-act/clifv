import FV.Backend.Proof.StockTerminalRoots
import FV.Backend.Proof.StockAluOperandCoverage
import FV.Backend.Proof.StockSelectionReceipts

/-! A complete driver actually sinks an atomic load through its extension
consumer, while the installed return placeholder remains unsunk. -/
namespace Backend.Stock.Proof.TerminalSinkWitness
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Coverage Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function : Clif.Function := {
  name := "stock_terminal_sink_provenance"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],body := [
    ⟨[31],.atomicLoad .i8 {} 7⟩,⟨[40],.extend .uextend .i64 31⟩],term := .ret [40]}] }
private def dataLoad := (instData function (.atomicLoad .i8 {} 7)).toOption.getD (.op .unit)
private def dataExtend := (instData function (.extend .uextend .i64 31)).toOption.getD (.op .unit)
private def dataReturn := (Backend.termData (.ret [40])).toOption.getD (.op .unit)
private def insts : Array IInfo := #[⟨dataLoad,[31],[.int 8],some (.atomicLoad .i8 {} 7)⟩,
  ⟨dataExtend,[40],[.int 64],some (.extend .uextend .i64 31)⟩,⟨dataReturn,[],[],none⟩]
private def fields (i : IInfo) := (i.data,i.results,i.resTys,i.clif)
private theorem fields_injective : Function.Injective fields := by
  intro a b equal
  cases a
  cases b
  simpa only [fields,Prod.mk.injEq,IInfo.mk.injEq] using equal
private def Observed : Prop := (Stock.lower function).toOption.map (fun result =>
  result.blockScans.toList.any (fun event => decide (event.ctx.insts.map fields = insts.map fields) &&
    event.output.records.any (fun record => record.inst == 1 &&
      decide (record.input.sunk = #[false,false,false]) &&
      decide (record.output.state.sunk = #[true,false,false]) &&
      record.output.step.any (fun step => step.decision == .emitted)))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
section Clean
attribute [local semireducible] Isle.Aarch64.program
private theorem clean {ctx : Ctx} (same : ctx.insts = insts) : Clean (sourceIdentityCtx ctx) := by
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [same] at lookup
  cases i with
  | zero => cases lookup; exact ⟨rfl,rfl⟩
  | succ i =>
    cases i with
    | zero => cases lookup; exact ⟨rfl,rfl⟩
    | succ i =>
      cases i with
      | zero => cases lookup; exact ⟨rfl,rfl⟩
      | succ i => simp [insts] at lookup

end Clean

/-- This original complete Stock driver performs a real source-effect sink.
The source-root preservation theorem is instantiated on that same actual
retained consumer, with a real in-bounds return slot and changed source sunk bit. -/
theorem stock_atomic_sink_terminal_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step)
      (out : V) (next : State) (rules : List RuleId),
      Stock.lower f = .ok result ∧ LowerScope f ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted ∧
      record.inst = 1 ∧ event.ctx.insts.size = 3 ∧ event.ctx.insts[2]!.clif = none ∧
      (scanState record.input record.inst).sunk = #[false,false,false] ∧ next.sunk = #[true,false,false] ∧
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) = .ok (some out,next,rules) ∧
      next.sunk[2]! = false := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error e => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,List.any_eq_true,Bool.and_eq_true,
      decide_eq_true_eq,beq_iff_eq,and_assoc] at actual
    obtain ⟨event,events,same,record,records,current,before,after,stepData⟩ := actual
    have same := (Array.map_inj_right fields_injective).mp same
    obtain ⟨step,recorded,emitted⟩ := (by simpa only [Option.any_eq_true,beq_iff_eq] using stepData :
      ∃ step,record.output.step = some step ∧ step.decision = .emitted)
    obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
    have mapped := (stock_lower_record_context run scope events).1
    have source : event.ctx.insts[record.inst]? = some insts[1]! := by rw [current,same]; rfl
    have clif : insts[1]!.clif = some (.extend .uextend .i64 31) := rfl
    have slot : event.ctx.insts[2]!.clif = none := by rw [same]; rfl
    have normalized : (scanState record.input record.inst).sunk = record.input.sunk := by
      unfold scanState; dsimp only; split <;> rfl
    have preserved := stock_statement_terminal_unsunk mapped (clean same) source clif receipt.rootRun slot
      (by rw [normalized,before]; rfl)
    have nextState : receipt.next.sunk = record.output.state.sunk := by
      have binding := receipt.binding
      exact (bindResults_noSink binding).symm.trans (congrArg State.sunk receipt.state.symm)
    refine ⟨function,result,event,record,step,receipt.out,receipt.next,receipt.fired,run,scope,events,
      records,recorded,emitted,current,by rw [same]; rfl,slot,normalized.trans before,nextState.trans after,receipt.rootRun,preserved⟩
end Backend.Stock.Proof.TerminalSinkWitness
