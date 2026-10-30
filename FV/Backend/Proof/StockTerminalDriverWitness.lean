import FV.Backend.Proof.StockTerminalDriver
import FV.Backend.Proof.StockTerminalSinkWitness

namespace Backend.Stock.Proof.TerminalDriverWitness
open Backend.Proof Backend.Proof.Driver Coverage Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- The complete actual atomic sink driver inhabits whole-traversal and every
retained-record invariant, while a real source instruction's sunk bit changes. -/
theorem stock_atomic_driver_unsunk_witness :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord)
      (step : Step) (out : V) (next : State) (rules : List RuleId),
      Stock.lower f = .ok result ∧ LowerScope f ∧ event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ record.inst = 1 ∧
      event.ctx.insts.size = 3 ∧ event.ctx.insts[2]!.clif = none ∧
      (scanState record.input record.inst).sunk = #[false,false,false] ∧ next.sunk = #[true,false,false] ∧
      Stock.runTerm event.ctx "lower" [.inst record.inst] (scanState record.input record.inst) = .ok (some out,next,rules) ∧
      TerminalUnsunk result.ctx result.final ∧ TerminalUnsunk result.ctx event.input ∧
      TerminalUnsunk result.ctx record.input ∧ TerminalUnsunk result.ctx record.output.state := by
  obtain ⟨f,result,event,record,step,out,next,rules,run,scope,events,records,recorded,emitted,current,
    size,slot,before,after,root,preserved⟩ := TerminalSinkWitness.stock_atomic_sink_terminal_witness
  have all := stock_lower_records_terminal_unsunk scope run events
  exact ⟨f,result,event,record,step,out,next,rules,run,scope,events,records,recorded,emitted,current,
    size,slot,before,after,root,stock_lower_terminal_unsunk scope run,all.1,(all.2 record records).1,(all.2 record records).2⟩

/-- Nonempty successor arguments exercise actual demand marking and the sunk
array frame used by synthetic nodes, with a real context build. -/
theorem stock_terminal_arguments_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial next : State),
      Stock.buildCtx f = .ok (ctx,ranges,initial) ∧
      branchArgs ctx initial 0 0 = .ok (#[.vreg 192 .int],next) ∧
      initial.demand[2]! = 0 ∧ next.demand[2]! = 1 ∧ next.sunk = initial.sunk := by
  obtain ⟨f,ctx,ranges,initial,next,build,run,before,after,old⟩ := branchArgs_noOpportunity_witness
  exact ⟨f,ctx,ranges,initial,next,build,run,before,after,stock_branchArgs_sunk run⟩

private def criticalFunction : Clif.Function := {
  name := "stock_terminal_critical_edges"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩]}
  blocks := [{id := 0,params := [(0,.i64)],term := .brif 0 ⟨1,[0]⟩ ⟨1,[0]⟩},
    {id := 1,params := [(1,.i64)],term := .ret [1]}] }
private def Observed : Prop := (Stock.lower criticalFunction).toOption.map (fun r =>
  decide (r.order.nodes.size = 4) && r.order.nodes.toList.any (fun | .edge .. => true | _ => false)) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
private theorem scope : LowerScope criticalFunction := lowerScope_of (by decide +kernel)
end Kernel
/-- Both original and synthetic critical-edge nodes occur in an actual complete
driver that satisfies the new whole-driver and retained-boundary invariant. -/
theorem stock_critical_driver_unsunk_witness :
    ∃ (f : Clif.Function) (result : Result),
      Stock.lower f = .ok result ∧ LowerScope f ∧ f.blocks.length = 2 ∧ result.order.nodes.size = 4 ∧
      (∃ pred k target,.edge pred k target ∈ result.order.nodes.toList) ∧
      TerminalUnsunk result.ctx result.final ∧ RecordsTerminalUnsunk result.ctx result.blockScans := by
  have evidence := observed
  unfold Observed at evidence
  cases run : Stock.lower criticalFunction with
  | error e => simp only [run,Except.toOption,Option.map_none] at evidence; cases evidence
  | ok result =>
    rw [run] at evidence
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq,List.any_eq_true] at evidence
    obtain ⟨size,node,member,edge⟩ := evidence
    have synthetic : ∃ pred k target,.edge pred k target ∈ result.order.nodes.toList := by
      cases node with
      | original b => cases edge
      | edge pred k target => exact ⟨pred,k,target,member⟩
    exact ⟨criticalFunction,result,run,scope,rfl,size,synthetic,stock_lower_terminal_unsunk scope run,
      fun event events => stock_lower_records_terminal_unsunk scope run events⟩
end Backend.Stock.Proof.TerminalDriverWitness
