module

public import FV.Backend.Proof.StockCriticalEdgeArity
public import FV.Backend.Proof.StockOutgoingVectors
public import FV.Backend.Proof.StockCfgTotal

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock

private def Collected (ctx : Ctx) (order : Order) (bi : Nat) (item : Nat × Nat) (args : Array Reg) : Prop :=
  match order.nodes[item.1]! with
  | .edge .. => args = #[]
  | .original _ => ∃ before after,branchArgs ctx before bi item.2 = .ok (args,after)
private theorem outgoing_vector {ctx : Ctx} {order : Order} {bi : Nat}
    {before after : State × Array (Array Reg)} {item : Nat × Nat}
    (run : outgoingStep ctx order bi before item = .ok after) :
    ∃ args,after.2 = before.2.push args ∧ Collected ctx order bi item args := by
  unfold outgoingStep at run
  cases tag : order.nodes[item.1]! with
  | edge pred index target =>
    simp only [tag,pure,Except.pure,Except.ok.injEq] at run
    subst after
    exact ⟨#[],rfl,by simp [Collected,tag]⟩
  | original target =>
    simp only [tag] at run
    cases call : branchArgs ctx before.1 bi item.2 with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨args,next⟩ := pair
      simp only [call,bind,Except.bind,pure,Except.pure,Except.ok.injEq] at run
      subst after
      exact ⟨args,rfl,by simp only [Collected,tag]; exact ⟨before.1,next,call⟩⟩
private theorem outgoing_fold {ctx : Ctx} {order : Order} {bi : Nat}
    {items : List (Nat × Nat)} {before after : State × Array (Array Reg)}
    (run : items.foldlM (outgoingStep ctx order bi) before = .ok after) :
    after.2.size = before.2.size + items.length ∧
    (∀ j,j < before.2.size → after.2[j]? = before.2[j]?) ∧
    (∀ j item,items[j]? = some item → ∃ args,
      after.2[before.2.size+j]? = some args ∧ Collected ctx order bi item args) := by
  induction items generalizing before with
  | nil =>
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq] at run
    subst after
    exact ⟨by simp,fun _ _ => rfl,fun j item h => by simp at h⟩
  | cons item rest ih =>
    rw [List.foldlM_cons] at run
    cases step : outgoingStep ctx order bi before item with
    | error e => simp only [step,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [step,bind,Except.bind] at run
      obtain ⟨args,installed,meaning⟩ := outgoing_vector step
      obtain ⟨size,prelude,selected⟩ := ih run
      have middleSize : middle.2.size = before.2.size + 1 := by simp [installed]
      refine ⟨by simpa [middleSize,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using size,?_,?_⟩
      · intro j bound
        rw [prelude j (by omega),installed,Array.getElem?_push]
        simp [bound,show j ≠ before.2.size by omega]
      · intro j pair found
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at found
          subst pair
          refine ⟨args,?_,meaning⟩
          rw [Nat.add_zero,prelude before.2.size (by omega),installed,Array.getElem?_push]
          simp
        | succ j =>
          simp only [List.getElem?_cons_succ] at found
          obtain ⟨vector,present,value⟩ := selected j pair found
          exact ⟨vector,by simpa [middleSize,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using present,value⟩
private theorem collected_at {ctx : Ctx} {order : Order} {bi index target : Nat}
    {targets : Array Nat} {before after : State} {outgoing : Array (Array Reg)}
    (run : collectOutgoing ctx order bi targets before = .ok (after,outgoing))
    (selected : targets[index]? = some target) :
    ∃ args,outgoing[index]? = some args ∧ Collected ctx order bi (target,index) args := by
  unfold collectOutgoing at run
  obtain ⟨_,_,present⟩ := outgoing_fold run
  have item : targets.zipIdx.toList[index]? = some (target,index) := by simpa using selected
  obtain ⟨args,found,meaning⟩ := present index (target,index) item
  exact ⟨args,by simpa using found,meaning⟩

private theorem core_outgoing {ctx : Ctx} {order : Order} {f : Clif.Function} {b : Clif.Block}
    {bi start stop : Nat} {data : Backend.V} {targets : Array Nat} {input : State} {core : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi start stop data targets input = .ok core) :
    ∃ before after,collectOutgoing ctx order bi targets before = .ok (after,core.outgoing) := by
  unfold lowerBlockCore at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨_,_,by assumption⟩

private theorem cfgSpec_unique {V : Array VBlock} {ss ss' : Array (Array Nat)}
    (left : Prep.CfgSpec V ss) (right : Prep.CfgSpec V ss') : ss = ss' := by
  apply Array.ext
  · rw [left.size,right.size]
  · intro b hb hb'
    have hV : b < V.size := by rw [← left.size]; exact hb
    obtain ⟨t,sb,back,_,atRow,count,targets⟩ := left.blk b V[b] (Array.getElem?_eq_getElem hV)
    obtain ⟨t',sb',back',_,atRow',count',targets'⟩ := right.blk b V[b] (Array.getElem?_eq_getElem hV)
    rw [back] at back'
    cases back'
    have row : ss[b] = sb := Option.some.inj (by rw [← Array.getElem?_eq_getElem hb]; exact atRow)
    have row' : ss'[b] = sb' := Option.some.inj (by rw [← Array.getElem?_eq_getElem hb']; exact atRow')
    rw [row,row']
    apply Array.ext
    · rw [count,count']
    · intro j hj hj'
      obtain ⟨l,hl⟩ : ∃ l,t.targets[j]? = some l :=
        ⟨_,List.getElem?_eq_getElem (by rw [← count]; exact hj)⟩
      obtain ⟨s,hs,find⟩ := targets j l hl
      obtain ⟨s',hs',find'⟩ := targets' j l hl
      rw [find] at find'
      cases find'
      rw [Array.getElem?_eq_getElem hj] at hs
      rw [Array.getElem?_eq_getElem hj'] at hs'
      exact (Option.some.inj hs).trans (Option.some.inj hs').symm


/-- Exact selected-edge argument/parameter count, against actual CFG indices. -/
def EdgeArityAt (vc : VCode) (edges : Array (Array (Array Reg))) (succs : Array (Array Nat)) : Prop :=
  ∀ (b j target : Nat) (ss : Array Nat) (row : Array (Array Reg)) (args : Array Reg) (tb : VBlock),
    succs[b]? = some ss → ss[j]? = some target → edges[b]? = some row → row[j]? = some args →
    vc.blocks[target]? = some tb → args.size = tb.params.size

private theorem original_arity {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {label bi j targetLabel : Nat} {ss : Array Nat} {row : Array (Array Reg)} {args : Array Reg} {tb : VBlock}
    (node : result.order.nodes[label]? = some (.original bi))
    (successors : result.order.successors[label]? = some ss) (edge : ss[j]? = some targetLabel)
    (outgoing : result.edgeArgs[label]? = some row) (atArgs : row[j]? = some args)
    (atTarget : result.code.blocks[targetLabel]? = some tb) : args.size = tb.params.size := by
  obtain ⟨source,id,sourceArgs,target,sourceAt,selected,found,classification⟩ :=
    stock_lower_indexed_successor_origin run node successors edge
  have successor : result.order.successors[label]![j]? = some targetLabel := by
    simpa only [getElem!_def,successors] using edge
  rcases classification with direct | synthetic
  · obtain ⟨ranges,input,data,core,lowered,stored⟩ := stock_lower_original_outgoing run node
    obtain ⟨before,after,collected⟩ := core_outgoing lowered
    obtain ⟨rawArgs,present,meaning⟩ := collected_at collected successor
    have targetNode : result.order.nodes[targetLabel]! = .original target := by simp only [getElem!_def,direct]
    simp only [Collected,targetNode] at meaning
    obtain ⟨start,stop,call⟩ := meaning
    obtain ⟨id',args',targetBlock,selected',lookup,count⟩ := stock_branchArgs_target_arity call
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
    have sourceBlock : result.ctx.func.blocks[bi]! = source := by simp only [func,getElem!_def,sourceAt]
    rw [sourceBlock,selected] at selected'
    cases selected'
    rw [func] at lookup
    have targetSource : f.blocks[target]? = some targetBlock := blockIdx_block found lookup
    have nonentry : target ≠ 0 := by
      intro zero
      rw [zero] at direct
      have labelZero := stock_blockOrder_original_unique (stock_lower_order run)
        (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) direct
        (stock_blockOrder_entry (stock_lower_order run) scope.nonempty)
      have member := Array.mem_toList_iff.mpr (Array.mem_of_getElem? edge)
      rw [labelZero] at member
      exact stock_lower_graph_nonentry run scope label ss successors member
    obtain ⟨block,placed,_,params⟩ := stock_lower_original_block_params run scope ssa direct targetSource nonentry
    rw [atTarget] at placed
    cases placed
    have actual : result.edgeArgs[label]?.bind (·[j]?) = some
        (rawArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) := by
      simp only [stored,Option.bind_some,Array.getElem?_map,present,Option.map_some]
    rw [outgoing,Option.bind_some,atArgs] at actual
    cases actual
    rw [Array.size_map,params]
    simp only [List.size_toArray,List.length_map,edgeParamNumbers,List.length_map]
    exact count
  · have empty := stock_lower_deferred_outgoing run node successor synthetic
    unfold outgoingAt at empty
    rw [outgoing,Option.bind_some,atArgs] at empty
    cases empty
    obtain ⟨input,next,raw,target,_,_,_,placed⟩ := stock_lower_critical_code run synthetic
    rw [atTarget] at placed
    cases placed
    rfl

private theorem computed_arity {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) :
    EdgeArityAt result.code result.edgeArgs result.order.successors := by
  intro label j target ss row args tb successors edge outgoing atArgs atTarget
  have inSuccs := (Array.getElem?_eq_some_iff.mp successors).1
  have dimensions := stock_prepare_dimensions run
  have cfgSize := (stock_lower_cfg run scope).size
  have bound : label < result.order.nodes.size := by omega
  cases tag : result.order.nodes[label] with
  | original bi =>
    have node : result.order.nodes[label]? = some (.original bi) := by rw [Array.getElem?_eq_getElem bound,tag]
    exact original_arity run scope ssa node successors edge outgoing atArgs atTarget
  | edge pred index sourceTarget =>
    have node : result.order.nodes[label]? = some (.edge pred index sourceTarget) := by rw [Array.getElem?_eq_getElem bound,tag]
    obtain ⟨targetLabel,block,vector,atSuccessors,_,placed,atOutgoing,count⟩ :=
      stock_lower_critical_edge_arity run scope ssa node
    rw [atSuccessors] at successors
    cases successors
    have jZero : j = 0 := by have h := (Array.getElem?_eq_some_iff.mp edge).1; simp only [Array.size_singleton] at h; omega
    subst j
    cases edge
    rw [atOutgoing] at outgoing
    cases outgoing
    cases atArgs
    change result.code.blocks[targetLabel]? = some tb at atTarget
    rw [atTarget] at placed
    cases placed
    exact count

/-- Every actual Stock CFG edge, ordinary/normal/exception/synthetic, has
exactly as many selected outgoing registers as its real target parameters.
All source selection, collection, graph routing, final aliasing and assembly
facts are derived under original scope/SSA. No edge-arity input filter or
caller graph/vector certificate is introduced. -/
theorem stock_lower_edge_arity {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup) :
    ∀ (ss ps : Array (Array Nat)),result.code.cfg = .ok (ss,ps) → EdgeArityAt result.code result.edgeArgs ss := by
  intro ss ps cfg
  have same := cfgSpec_unique (Backend.Proof.Prep.cfg_spec cfg) (stock_lower_cfg run scope)
  rw [same]
  exact computed_arity run scope ssa

end Backend.Stock.Proof
