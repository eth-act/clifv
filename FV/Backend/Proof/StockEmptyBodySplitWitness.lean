import FV.Backend.Proof.StockBodyScanOrigin

namespace Backend.Stock.Proof.EmptyBodySplitWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
private def function : Clif.Function := {
  name := "stock_empty_body_split"
  sig := {params := [],returns := [],callConv := some .systemV}
  blocks := [{id := 0,params := [],body := [],term := .ret []}] }
private def frame : Clif.Frame := {
  func := function,regs := fun _ => none,slots := [],body := [],term := .ret [] }
private def Observed : Prop := (Stock.lower function).toOption.map (fun result =>
  result.blockScans.toList.any (fun event => event.block == 0 && decide (event.output.code = #[.rets []]))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)

/-- A complete zero-statement function inhabits the split's empty-body boundary.
The actual remaining scan code executes a machine return, and the original
source step returns the same empty value list. -/
theorem stock_empty_body_split_witness :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block) (term : ScanRecord) (body : BlockScan),
      Stock.lower function = .ok result ∧ LowerScope function ∧ event ∈ result.blockScans.toList ∧
      SourceBodySplit function event b term body ∧ event.block = 0 ∧ b.body = [] ∧
      term.inst = 0 ∧ body.records = [] ∧ body.code = #[] ∧ body.state = term.output.state ∧
      event.output.code = #[.rets []] ∧ term.output.emitted = #[.rets []] ∧
      Clif.step Clif.Env.empty {funcs := []} ⟨frame,[],Clif.Mem.empty⟩ = .done [] Clif.Mem.empty ∧
      ∀ ρ world, seqRun ispec (event.output.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
          some (.stop 0 (.rets []) #[] ρ world [] world .ret) := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,List.any_eq_true,
      Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at actual
    obtain ⟨event,events,blockIndex,code⟩ := actual
    obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
    have blockEq : b = function.blocks[0]! := by
      have found := split.block
      rw [blockIndex] at found
      exact Option.some.inj found.symm
    have empty : b.body = [] := by rw [blockEq]; rfl
    have termIndex : term.inst = 0 := by rw [split.termInst,split.termIndex,blockIndex,empty]; rfl
    have records : body.records = [] := by
      have order := split.scanned.order
      simp only [sourceBodyIndices,empty,List.length_nil,List.range_zero,List.map_nil,List.reverse_nil] at order
      exact List.map_eq_nil_iff.mp order
    have bodyCode : body.code = #[] := by
      have exactCode := split.scanned.code
      rw [records] at exactCode
      exact Array.toList_inj.mp exactCode
    have state : body.state = term.output.state := by
      have chain := split.scanned.chain
      simpa only [records,StateChain] using chain
    have termCode : term.output.emitted = #[.rets []] := by
      have joined := split.code
      rw [code,bodyCode,Array.empty_append] at joined
      exact joined.symm
    refine ⟨result,event,b,term,body,rfl,scope,events,split,blockIndex,empty,termIndex,records,bodyCode,state,code,termCode,rfl,?_⟩
    intro ρ world
    rw [code]
    rfl
end Backend.Stock.Proof.EmptyBodySplitWitness
