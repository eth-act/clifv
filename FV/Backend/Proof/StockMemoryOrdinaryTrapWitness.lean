import FV.Backend.Proof.StockMemoryOrdinarySourceContinuation
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.OrdinaryBody.TrapFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def flags : Clif.MemFlags := {trapCode := some .heapOob}
private def block : Clif.Block := {
  id := 0,params := [(0,.i64)],
  body := [⟨[],.nop⟩,⟨[1],.load .load .i64 flags 0 0⟩],term := .ret [1] }
private def function : Clif.Function := {
  name := "stock_memory_first_trap_witness",
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV},
  blocks := [block] }
private def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 0 ⟨.i64,0⟩,slots := [],body := block.body,term := block.term }
private def observed : Option Bool := (Stock.lower function).toOption.map fun result =>
  lowerScopeB function && result.blockScans.toList.any (fun event => event.block == 0)
private theorem observed_true : observed = some true := by native_decide

/-- A genuine memory trap follows a successful NOP in an actual lowered function.
The complete source run supplies the indexed first-trap prefix internally. -/
theorem ordinary_memory_first_trap_witness :
    ∃ (result : Result) (event : BlockScanEvent) (term : ScanRecord) (body : BlockScan),
      Stock.lower function = .ok result ∧ LowerScope function ∧ event ∈ result.blockScans.toList ∧
      SourceBodySplit function event block term body ∧
      Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],Clif.Mem.empty⟩ = .trapped .heapOob ∧
      SourceTrapSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx event.block)
        (LocalBody.IndexedSourceTrap Clif.Env.empty {funcs := []} function event.ctx event.block)
        (sourceBodyIndices function event.block block).reverse (0,initial,Clif.Mem.empty) .heapOob := by
  have actual := observed_true
  unfold observed at actual
  cases run : Stock.lower function with
  | error message => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      List.any_eq_true,beq_iff_eq] at actual
    obtain ⟨scopeB,event,events,atBlock⟩ := actual
    have scope := lowerScope_of scopeB
    have source : function.blocks[event.block]? = some block := by rw [atBlock]; rfl
    obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
    have same : b = block := Option.some.inj (split.block.symm.trans source)
    subst b
    have trapped : Clif.runLoop Clif.Env.empty {funcs := []} 2 ⟨initial,[],Clif.Mem.empty⟩ = .trapped .heapOob := rfl
    have family : ∀ stm ∈ block.body,OrdinaryInst stm.inst := by
      intro stm member
      simp only [block,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      all_goals simp [OrdinaryInst]
    rcases actual_ordinary_source_trap_or_continue run events split family
        (env := Clif.Env.empty) (cp := {funcs := []}) (j := 0) (by decide) (s := ⟨initial,[],Clif.Mem.empty⟩)
        rfl trapped with failed | ⟨t,left,total,continued,empty,steps,frame⟩
    · refine ⟨result,event,term,body,rfl,scope,events,split,trapped,?_⟩
      simpa only [sourceBodyIndices,List.reverse_reverse,List.range'_eq_map_range,Nat.add_zero,Nat.sub_zero] using failed
    · have zero : left = 0 := by change left+2 = 2 at total; omega
      rw [zero] at continued
      cases continued

end Backend.Stock.Proof.OrdinaryBody.TrapFixture
