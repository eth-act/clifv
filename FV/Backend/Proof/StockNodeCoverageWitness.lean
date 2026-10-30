import FV.Backend.Proof.StockEntryOrder
import FV.Backend.Proof.StockNodeCoverage
import FV.Backend.Proof.StockBranchHelperProjection
import FV.Backend.Proof.StockTerminalDriverWitness
import FV.Backend.Proof.StockControlCfgWitness
import FV.Backend.Proof.StockTermContractWitness
import FV.Backend.Proof.StockPerEdgeCheckerWitness

namespace Backend.Stock.Proof.NodeCoverageWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 2000
set_option maxHeartbeats 8000000

/-- A complete actual critical-edge driver has both original and synthetic
nodes; every original, including entry0, has a real retained scan. -/
theorem stock_original_scan_coverage_witness :
    ∃ (f : Clif.Function) (result : Result),Stock.lower f = .ok result ∧ LowerScope f ∧
      result.order.nodes[0]? = some (.original 0) ∧
      (∃ pred index target,Node.edge pred index target ∈ result.order.nodes.toList) ∧
      ∀ (label bi : Nat),result.order.nodes[label]? = some (.original bi) →
        ∃ event,event ∈ result.blockScans.toList ∧ event.block = bi := by
  obtain ⟨f,result,run,scope,_,_,edges,_⟩ := TerminalDriverWitness.stock_critical_driver_unsunk_witness
  exact ⟨f,result,run,scope,stock_blockOrder_entry (stock_lower_order run) scope.nonempty,edges,
    fun _ _ node => stock_lower_original_scan run node⟩

/-- Complete scalar/two-result/sret source fixtures inhabit the terminal CFG
clause at their actual original node index, without a scan premise. -/
theorem stock_return_node_cfg_witness (p : ReturnFixture.Case) :
    ∃ (result : Result) (vb : VBlock) (last : MInst),
      Stock.lower (ReturnFixture.function p) = .ok result ∧ LowerScope (ReturnFixture.function p) ∧
      Dominated (ReturnFixture.function p) ∧ result.order.nodes[0]? = some (.original 0) ∧
      result.code.blocks[0]? = some vb ∧ vb.insts.back? = some last ∧ last.isTerminator = true ∧
      last.targets = [] ∧ result.order.successors[0]? = some #[] := by
  obtain ⟨result,event,label,vb,last,rs,ps,run,scope,dominated,_⟩ := ControlCfgWitness.stock_return_cfg_witness p
  have node := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨vb,last,placed,back,ends,targets,successors⟩ := stock_lower_terminal_cfg_at run scope node
    (b := (ReturnFixture.function p).blocks[0]!) (by rfl) (by rfl)
  exact ⟨result,vb,last,run,scope,dominated,node,placed,back,ends,targets,successors⟩

private def trapFunction : Clif.Function := {
  name := "stock_trap_abi_contract",sig := {callConv := some .systemV}
  blocks := [{id := 0,term := .trap (.user 9)}] }
/-- A complete source trap inhabits the exact node-indexed terminal CFG case. -/
theorem stock_trap_node_cfg_witness : ∃ (result : Result) (vb : VBlock) (last : MInst),
    Stock.lower trapFunction = .ok result ∧ LowerScope trapFunction ∧ Dominated trapFunction ∧
    result.order.nodes[0]? = some (.original 0) ∧ result.code.blocks[0]? = some vb ∧
    vb.insts.back? = some last ∧ last.isTerminator = true ∧ last.targets = [] ∧
    result.order.successors[0]? = some #[] := by
  obtain ⟨result,run,scope,_⟩ := TermContractWitness.stock_trap_term_contract_witness
  change Stock.lower trapFunction = .ok result at run
  change LowerScope trapFunction at scope
  have node := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
  obtain ⟨vb,last,placed,back,ends,targets,successors⟩ := stock_lower_terminal_cfg_at run scope node
    (b := trapFunction.blocks[0]!) (by rfl) (by rfl)
  exact ⟨result,vb,last,run,scope,dominated_of (by decide +kernel),node,placed,back,ends,targets,successors⟩

private def conditionalFunction : Clif.Function := {
  name := "stock_per_successor_migration"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[7]⟩ ⟨2,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .ret [31]}, {id := 2,params := [(47,.i64)],term := .ret [47]}] }
private def compare : V := .data 58 4 [.data 59 10 [],.data 93 0 [],.reg .xzr,
  .reg (.vreg 192 .int),.op (.imm12 ⟨0,false⟩)]
private def condition (kind : Fin 5) : V := match kind.val with
  | 0 => .data 123 0 [.reg (.vreg 192 .int),.data 93 0 []]
  | 1 => .data 123 1 [.reg (.vreg 192 .int),.data 93 1 []]
  | 2 => .data 123 2 [.data 47 1 [compare],.data 96 0 []]
  | 3 => .data 123 3 [.data 47 1 [compare],.data 96 0 [],.data 96 1 []]
  | _ => .data 123 4 [.data 47 1 [compare],.data 96 0 [],.data 96 1 []]
private def helperArgs (kind : Fin 5) : List V := [condition kind,.label 2,.label 1]
private def conditionalBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx conditionalFunction).toOption.getD (sinkCtx,#[],sinkState)
private theorem conditional_build : Stock.buildCtx conditionalFunction = .ok conditionalBuilt := rfl
private theorem lower_build {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,by assumption⟩

private theorem helper_success (kind : Fin 5) :
    ((applyTerm program (Stock.sem conditionalBuilt.1) {} 200 46 722 (helperArgs kind)).run
      (conditionalBuilt.2.2,#[])).toOption.map (fun q => q.1.isSome) = some true := by
  have cases : kind.val = 0 ∨ kind.val = 1 ∨ kind.val = 2 ∨ kind.val = 3 ∨ kind.val = 4 := by omega
  rcases cases with h | h | h | h | h <;> simp only [helperArgs,condition,h] <;> decide +kernel

/-- Every condition-result form succeeds in the actual helper from a complete
original-scope/dominated conditional Stock program and projects exactly to the
legacy machine-code state. This includes both combined-flag fallback forms. -/
theorem stock_branch_helper_projection_witness (kind : Fin 5) :
    ∃ (result : Result) (out : V) (next : State) (trace : Array RuleId),
      Stock.lower conditionalFunction = .ok result ∧ LowerScope conditionalFunction ∧ Dominated conditionalFunction ∧
      (applyTerm program (Stock.sem result.ctx) {} 200 46 722 (helperArgs kind)).run (result.initial,#[]) =
        .ok (some out,next,trace) ∧
      (applyTerm program (Backend.sem result.ctx) {} 200 46 722 (helperArgs kind)).run (result.initial.base,#[]) =
        .ok (some out,next.base,trace) := by
  obtain ⟨result,run,scope,dominated,_⟩ := PerEdgeCheckerWitness.stock_per_edge_checker_witness
  change Stock.lower conditionalFunction = .ok result at run
  change LowerScope conditionalFunction at scope
  change Dominated conditionalFunction at dominated
  obtain ⟨ranges,build⟩ := lower_build run
  have same := Except.ok.inj (build.symm.trans conditional_build)
  have context := congrArg Prod.fst same
  have initial := congrArg (fun p => p.2.2) same
  have success := helper_success kind
  rw [← context,← initial] at success
  cases actual : (applyTerm program (Stock.sem result.ctx) {} 200 46 722 (helperArgs kind)).run (result.initial,#[]) with
  | error e => simp only [actual,Except.toOption,Option.map_none] at success; cases success
  | ok q =>
    obtain ⟨out,next,trace⟩ := q
    cases out with
    | none => simp only [actual,Except.toOption,Option.map_some,Option.isSome] at success; cases success
    | some out =>
      have projected := BranchHelpers.stock_br_cond_result_projects result.ctx {} rfl 200 (helperArgs kind) result.initial #[]
      rw [actual] at projected
      exact ⟨result,out,next,trace,run,scope,dominated,actual,projected.symm⟩

end Backend.Stock.Proof.NodeCoverageWitness
