import FV.Backend.Proof.StockTerminalCfg
import FV.Backend.Proof.StockReturnSourceWitness

namespace Backend.Stock.Proof.ControlCfgWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

private def jumpFunction : Clif.Function := {
  name := "stock_jump_shape",sig := {callConv := some .systemV}
  blocks := [{id := 0,term := .jump ⟨1,[]⟩},{id := 1,term := .ret []}] }
private def jumpBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx jumpFunction).toOption.getD (sinkCtx,#[],sinkState)
private def jumpCtx := Driver.termCtx jumpBuilt.1 0 (.data 152 15 [.data 151 0 [],.op .unit])
private def jumpNext := {jumpBuilt.2.2 with base := jumpBuilt.2.2.base.emit (.jump 1)}
private theorem jump_success : (Stock.lower jumpFunction).isOk = true := by decide +kernel
private theorem jump_scope : LowerScope jumpFunction := lowerScope_of (by decide +kernel)
private theorem jump_dominated : Dominated jumpFunction := dominated_of (by decide +kernel)
private theorem jump_call : Stock.runTerm jumpCtx "lower_branch" [.inst 0,.labels [1]] jumpBuilt.2.2 =
    .ok (some (.op .unit),jumpNext,[559,6,1139]) := by rfl

/-- A complete original-scope/dominated jump program inhabits actual first-match
branch selection and the exact named jump-root state/target theorem. -/
theorem stock_jump_shape_witness :
    ∃ (result : Result) (ctx : Ctx) (st next : State),
      Stock.lower jumpFunction = .ok result ∧ LowerScope jumpFunction ∧ Dominated jumpFunction ∧
      Stock.runTerm ctx "lower_branch" [.inst 0,.labels [1]] st = .ok (some (.op .unit),next,[559,6,1139]) ∧
      Nonempty (BranchSelection ctx 0 [1] st (.op .unit) next [559,6,1139]) ∧
      ∃ label,[1] = [label] ∧ next = {st with base := st.base.emit (.jump label)} ∧
        ([559,6,1139] : List RuleId).getLast? = some rule_lower_3270.id := by
  have success := jump_success
  cases run : Stock.lower jumpFunction with
  | error e => simp only [run,Except.isOk] at success; cases success
  | ok result =>
    have slot : jumpCtx.insts[0]? = some ⟨.data 152 15 [.data 151 0 [],.op .unit],[],[],none⟩ := rfl
    obtain ⟨label,target,state,_,last⟩ := Control.stock_named_jump_shape slot jump_call
    exact ⟨result,jumpCtx,jumpBuilt.2.2,jumpNext,rfl,jump_scope,jump_dominated,jump_call,
      stock_named_branch_selection jump_call,label,target,state,last⟩

private def trapFunction : Clif.Function := {
  name := "stock_terminal_cfg_trap",sig := {callConv := some .systemV}
  blocks := [{id := 0,term := .trap (.user 9)}] }
private def trapBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx trapFunction).toOption.getD (sinkCtx,#[],sinkState)
private def trapCtx := Driver.termCtx trapBuilt.1 0 (.data 152 26 [.data 151 4 [],.op (.trapCode (.user 9))])
private def trapNext := {trapBuilt.2.2 with base := trapBuilt.2.2.base.emit (.udf (.user 9))}
private theorem trap_observed : (Stock.lower trapFunction).toOption.map
    (fun r => r.blockScans.toList.any (fun e => e.block == 0)) = some true := by decide +kernel
private theorem trap_scope : LowerScope trapFunction := lowerScope_of (by decide +kernel)
private theorem trap_dominated : Dominated trapFunction := dominated_of (by decide +kernel)
private theorem trap_call : Stock.runTerm trapCtx "lower" [.inst 0] trapBuilt.2.2 =
    .ok (some (.regsVec []),trapNext,[297,6,9,964]) := by rfl

/-- A complete coded-trap program inhabits the exact named root and actual
assembled UDF/empty-successor CFG clause under original source conditions. -/
theorem stock_trap_cfg_witness : ∃ (result : Result) (event : BlockScanEvent) (label : Nat) (vb : VBlock),
    Stock.lower trapFunction = .ok result ∧ LowerScope trapFunction ∧ Dominated trapFunction ∧
    event ∈ result.blockScans.toList ∧ event.output.code.back? = some (.udf (.user 9)) ∧
    result.order.nodes[label]? = some (.original event.block) ∧
    result.code.blocks[label]? = some vb ∧ vb.insts.back? = some (.udf (.user 9)) ∧
    result.order.successors[label]? = some #[] ∧
    trapNext = {trapBuilt.2.2 with base := trapBuilt.2.2.base.emit (.udf (.user 9))} ∧
    ([297,6,9,964] : List RuleId).getLast? = some rule_lower_2237.id := by
  have observed := trap_observed
  cases run : Stock.lower trapFunction with
  | error e => simp only [run,Except.toOption,Option.map_none] at observed; cases observed
  | ok result =>
    rw [run] at observed
    simp only [Except.toOption,Option.map_some,Option.some.injEq,List.any_eq_true,beq_iff_eq] at observed
    obtain ⟨event,events,zero⟩ := observed
    have block : trapFunction.blocks[event.block]? = some trapFunction.blocks[0]! := by rw [zero]; rfl
    have atScan := stock_lower_trap_scan_last run trap_scope events block rfl
    obtain ⟨label,vb,node,placed,last,successors⟩ := stock_lower_trap_cfg run trap_scope events block rfl
    have slot : trapCtx.insts[0]? = some ⟨.data 152 26 [.data 151 4 [],.op (.trapCode (.user 9))],[],[],none⟩ := rfl
    obtain ⟨state,_,root⟩ := Control.stock_named_trap_shape slot trap_call
    exact ⟨result,event,label,vb,rfl,trap_scope,trap_dominated,events,atScan,node,placed,last,successors,state,root⟩

/-- All supported scalar-width/two-result and implicit-sret complete source
return fixtures inhabit the actual scan suffix and assembled return CFG clause. -/
theorem stock_return_cfg_witness (p : ReturnFixture.Case) :
    ∃ (result : Result) (event : BlockScanEvent) (label : Nat) (vb : VBlock) (last : MInst)
      (rs ps : List Reg),
      Stock.lower (ReturnFixture.function p) = .ok result ∧ LowerScope (ReturnFixture.function p) ∧
      Dominated (ReturnFixture.function p) ∧ event ∈ result.blockScans.toList ∧
      event.output.code.back? = some (.rets (rs.zip ps)) ∧ returnPins (ReturnFixture.function p) rs.length = some ps ∧
      result.order.nodes[label]? = some (.original event.block) ∧ result.code.blocks[label]? = some vb ∧
      vb.insts.back? = some last ∧ last.isTerminator = true ∧ last.targets = [] ∧
      result.order.successors[label]? = some #[] := by
  obtain ⟨result,event,record,step,extra,run,scope,dominated,_,events,_⟩ :=
    ReturnSourceWitness.stock_return_auto_source_witness p 0 0
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have zero : event.block = 0 := by
    have bound := lt_of_getElem? split.block
    have small : event.block < 1 := by simpa [ReturnFixture.function] using bound
    omega
  have block : (ReturnFixture.function p).blocks[event.block]? = some (ReturnFixture.function p).blocks[0]! := by
    rw [zero]; rfl
  obtain ⟨rs,ps,atScan,pins⟩ := stock_lower_return_scan_last run scope events block (xs := ReturnFixture.explicitXs p) rfl
  obtain ⟨label,vb,last,node,placed,atLast,terminal,targets,successors⟩ :=
    stock_lower_return_cfg run scope events block (xs := ReturnFixture.explicitXs p) rfl
  exact ⟨result,event,label,vb,last,rs,ps,run,scope,dominated,events,atScan,pins,node,placed,atLast,terminal,targets,successors⟩

end Backend.Stock.Proof.ControlCfgWitness
