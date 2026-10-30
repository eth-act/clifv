import FV.Backend.Proof.StockOrderGraph
import FV.Backend.Proof.StockEntryOrder
import FV.Backend.Proof.StockGraphEdges
import FV.Backend.Proof.StockOutgoingOrigin

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def argStep (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (acc : State × Array Reg) : Except String (ForInStep (State × Array Reg)) := do
  match arg with
  | .val v =>
    let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
    pure (.yield (acc.1.mark v,acc.2.push r))
  | .ret i =>
    if index < nh then throw "try_call return on exception edge"
    let some r := rets[i]? | throw "try_call return index"
    pure (.yield (acc.1,acc.2.push r))
  | .exn i =>
    if index == nh then throw "try_call payload on normal edge"
    let some r := pays[i]? | throw "try_call payload index"
    pure (.yield (acc.1,acc.2.push r))

private theorem step_count {ctx : Ctx} {rets pays : List Reg} {index nh : Nat}
    {arg : Clif.TryArg} {input output : State × Array Reg}
    (run : argStep ctx rets pays index nh arg input = .ok (.yield output)) : output.2.size = input.2.size+1 := by
  cases arg <;> simp only [argStep,bind,Except.bind,pure,Except.pure] at run
  all_goals repeat' first
    | (solve | cases run)
    | (solve | cases run; simp)
    | simp only [bind,Except.bind,pure,Except.pure,throw,throwThe,MonadExceptOf.throw] at run
    | split at run
private theorem step_not_done (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (input output : State × Array Reg) :
    argStep ctx rets pays index nh arg input ≠ .ok (.done output) := by
  cases arg <;> simp only [argStep,bind,Except.bind,pure,Except.pure]
  all_goals repeat' split
  all_goals simp [pure,Except.pure,bind,Except.bind]
private theorem loop_count {ctx : Ctx} {rets pays : List Reg} {index nh : Nat}
    {xs : List Clif.TryArg} {input output : State × Array Reg}
    (run : forIn xs input (argStep ctx rets pays index nh) = .ok output) :
    output.2.size = input.2.size + xs.length := by
  induction xs generalizing input with
  | nil => cases run; simp
  | cons x xs ih =>
    rw [List.forIn_cons] at run
    cases first : argStep ctx rets pays index nh x input with
    | error err => simp only [first,bind,Except.bind] at run; cases run
    | ok step =>
      cases step with
      | done stop => exact False.elim (step_not_done _ _ _ _ _ _ _ _ first)
      | yield mid =>
        simp only [first,bind,Except.bind] at run
        have tail := ih run
        have head := step_count first
        simp only [List.length_cons]
        omega

/-- Successful actual selected argument collection determines its original
source successor and exact target arity, independently of register classes or
reservation-state assumptions. This is a consequence of execution, not a new
source acceptance check. -/
theorem stock_branchArgs_target_arity {ctx : Ctx} {input next : State} {bi j : Nat} {args : Array Reg}
    (call : branchArgs ctx input bi j = .ok (args,next)) :
    ∃ (id : Nat) (sourceArgs : List Clif.TryArg) (target : Clif.Block),
      (destinations ctx.func.blocks[bi]!.term)[j]? = some (id,sourceArgs) ∧
      ctx.func.block? id = some target ∧ args.size = target.params.length := by
  unfold branchArgs at call
  dsimp only at call
  cases selected : (destinations ctx.func.blocks[bi]!.term)[j]? with
  | none => simp only [selected] at call; cases call
  | some pair =>
    obtain ⟨id,sourceArgs⟩ := pair
    rw [selected] at call
    dsimp only at call
    cases found : ctx.func.block? id with
    | none => simp only [found] at call; cases call
    | some target =>
      rw [found] at call
      dsimp only at call
      split at call
      · cases call
      · rename_i arity
        let b := ctx.func.blocks[bi]!
        let ti := (input.instBlock.findIdx? (· == bi)).getD 0 + b.body.length
        let nh := match b.term with
          | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
          | _ => 0
        change (do
          let pair ← forIn sourceArgs (input,#[])
            (argStep ctx (input.tryRegs[ti]!).1 (input.tryRegs[ti]!).2 j nh)
          pure (pair.2,pair.1)) = .ok (args,next) at call
        cases loop : forIn sourceArgs (input,#[]) (argStep ctx (input.tryRegs[ti]!).1 (input.tryRegs[ti]!).2 j nh) with
        | error err => simp only [loop,bind,Except.bind] at call; cases call
        | ok pair =>
          obtain ⟨state,rs⟩ := pair
          rw [loop] at call
          simp only [bind,Except.bind,pure,Except.pure] at call
          cases call
          have count := loop_count loop
          have sameArity : sourceArgs.length = target.params.length := by simpa using arity
          exact ⟨id,sourceArgs,target,rfl,found,by simpa only [Array.size_empty,Nat.zero_add,sameArity] using count⟩

/-- Every actual Stock critical edge passes exactly its real original target's
parameter count. Source-edge provenance, target lookup, collection, final
aliasing and actual original-block parameter assembly are connected internally. -/
theorem stock_lower_critical_edge_arity {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {label pred index target : Nat} (node : result.order.nodes[label]? = some (.edge pred index target)) :
    ∃ (targetLabel : Nat) (tb : VBlock) (args : Array Reg),
      result.order.successors[label]? = some #[targetLabel] ∧
      result.order.nodes[targetLabel]? = some (.original target) ∧
      result.code.blocks[targetLabel]? = some tb ∧ result.edgeArgs[label]? = some #[args] ∧ args.size = tb.params.size := by
  obtain ⟨source,id,sourceArgs,atSource,selected,found⟩ := stock_lower_critical_source run node
  obtain ⟨input,next,args,collected,outgoing⟩ := stock_lower_critical_outgoing run node
  obtain ⟨targetLabel,row,targetNode⟩ := stock_lower_edge_successor run node
  have built : ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
    unfold Stock.lower at run
    dsimp only at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run
    cases run
    exact ⟨_,by assumption⟩
  obtain ⟨ranges,build⟩ := built
  have func := (buildCtx_mappedInv scope build).func
  obtain ⟨id',args',targetBlock,selected',lookup,count⟩ := stock_branchArgs_target_arity collected
  have sourceBlock : result.ctx.func.blocks[pred]! = source := by simp only [func,getElem!_def,atSource]
  rw [sourceBlock,selected] at selected'
  cases selected'
  rw [func] at lookup
  have targetAt : f.blocks[target]? = some targetBlock := blockIdx_block found lookup
  have nonentry : target ≠ 0 := by
    intro zero
    subst target
    exact stock_blockOrder_edges_nonentry (stock_lower_order run) scope pred index
      (Array.mem_toList_iff.mpr (Array.mem_of_getElem? node))
  obtain ⟨tb,atTarget,_,parameters⟩ := stock_lower_original_block_params run scope ssa targetNode targetAt nonentry
  refine ⟨targetLabel,tb,args.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)),
    row,targetNode,atTarget,outgoing,?_⟩
  rw [Array.size_map,parameters]
  simp only [List.size_toArray,List.length_map,edgeParamNumbers,List.length_map]
  exact count

end Backend.Stock.Proof
