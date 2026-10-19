import FV.Backend.Proof.StockOrdinaryCfg
import FV.Backend.Proof.StockControlShape

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock

private theorem named_jump {ctx : Ctx} {f : Clif.Function} {dest : Clif.BlockCall}
    {ti : Nat} {data : V} {labels : List Label} {before next : State} {out : V} {trace : List RuleId}
    (prepared : Coverage.blockData f (.jump dest) = .ok data)
    (slot : ctx.insts[ti]? = some ⟨data,[],[],none⟩)
    (run : Stock.runTerm ctx "lower_branch" [.inst ti,.labels labels] before = .ok (some out,next,trace)) :
    ∃ label,labels = [label] ∧ next.base.emitted.back? = some (.jump label) := by
  simp only [Coverage.blockData,abiTerm,termData_jump] at prepared
  cases prepared
  obtain ⟨label,labelsEq,state,_,_⟩ := Control.stock_named_jump_shape slot run
  exact ⟨label,labelsEq,by rw [state]; simp [LState.emit]⟩
private theorem branch_jump {ctx : Ctx} {f : Clif.Function} {dest : Clif.BlockCall}
    {bi ti : Nat} {data : V} {labels : Array Nat} {input : State} {out : BranchEmission}
    (prepared : Coverage.blockData f (.jump dest) = .ok data)
    (slot : ctx.insts[ti]? = some ⟨data,[],[],none⟩)
    (run : emitBranch ctx f (.jump dest) bi ti labels input = .ok out) :
    ∃ label,labels.toList = [label] ∧ out.code.back? = some (.jump label) := by
  let before : State := {input with current := some ti,color := none,base.emitted := #[]}
  unfold emitBranch at run
  change (do
    let (v,next,fired) ← Stock.runTerm ctx "lower_branch" [.inst ti,.labels labels.toList] before
    if v.isNone then throw s!"no lowering rule for terminator {repr (Clif.Terminator.jump dest)}"
    let code ← branchCode f (.jump dest) labels next.base.emitted
    pure (⟨next,code,⟨bi,ti,.emitted,before,next,[],fired,code⟩,fired⟩ : BranchEmission)) = .ok out at run
  cases call : Stock.runTerm ctx "lower_branch" [.inst ti,.labels labels.toList] before with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok q =>
    obtain ⟨v,next,fired⟩ := q
    simp only [call,bind,Except.bind] at run
    cases v with
    | none => simp at run
    | some v =>
      simp only [Option.isNone_some,Bool.false_eq_true,ite_false] at run
      have code : branchCode f (.jump dest) labels next.base.emitted = .ok next.base.emitted := rfl
      simp only [code,bind,Except.bind,pure,Except.pure] at run
      cases run
      exact named_jump prepared slot call
private theorem map_some_inv {α : Type} {call : Except String α} {out : Option α}
    (run : (some <$> call) = .ok out) : ∃ value,call = .ok value ∧ out = some value := by
  cases call with
  | error e => cases run
  | ok value => cases run; exact ⟨value,rfl,rfl⟩
private theorem append_last {α : Type} {left right : Array α} {last : α}
    (back : right.back? = some last) : (left ++ right).back? = some last := by
  rw [Array.back?_append]
  simp only [back]
  rfl
private theorem core_jump {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {dest : Clif.BlockCall} {bi start stop : Nat} {data : V} {labels : Array Nat}
    {input : State} {out : LoweredBlockCore}
    (term : b.term = .jump dest) (prepared : Coverage.blockData f b.term = .ok data)
    (bound : stop-1 < ctx.insts.size)
    (run : lowerBlockCore ctx order f b bi start stop data labels input = .ok out) :
    ∃ label,labels.toList = [label] ∧ out.code.back? = some (.jump label) := by
  have slot : ({ctx with insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩,tryRegs := input.tryRegs[stop-1]!} : Ctx).insts[stop-1]? = some ⟨data,[],[],none⟩ := by
    simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]
  unfold lowerBlockCore at run
  simp only [term,ite_true] at run
  repeat' first
    | (solve | contradiction)
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure,Functor.map,Except.map] at run
    | split at run
  all_goals
    cases run
    rename_i _ branch branchRun _ outgoing outgoingRun _ scan scanRun
    obtain ⟨emission,emitted,wrapped⟩ := map_some_inv branchRun
    subst branch
    rw [term] at prepared
    obtain ⟨label,targets,back⟩ := branch_jump prepared slot emitted
    exact ⟨label,targets,append_last back⟩

/-- Every actual original source jump ends in the exact emitted MInst.jump
whose target is its real singleton graph row. Original core selection, body
scan, assembly, reverse traversal and final aliasing are derived internally. -/
theorem stock_lower_original_jump_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {label bi : Nat} {b : Clif.Block} {dest : Clif.BlockCall}
    (node : result.order.nodes[label]? = some (.original bi))
    (sourceBlock : f.blocks[bi]? = some b) (term : b.term = .jump dest) :
    ∃ (target : Label) (block : VBlock),result.code.blocks[label]? = some block ∧
      block.insts.back? = some (.jump target) ∧ result.order.successors[label]? = some #[target] := by
  obtain ⟨ranges,params,input,data,core,block,preludeCode,lowered,assembled,build,prepared,placed,suffix⟩ :=
    OrdinaryCfg.stock_lower_original_code_origin run node
  have sourceBang : f.blocks[bi]! = b := by rw [getElem!_def,sourceBlock]
  rw [sourceBang] at lowered prepared
  obtain ⟨original,oldState,oldBuild,spec,view⟩ := buildCtx_source build
  have range : ranges[bi]! = (blockStart f bi,blockStart f bi+b.body.length+1) := by
    simp only [getElem!_def,spec.ranges bi b sourceBlock]
  have placeholder : result.ctx.insts[blockStart f bi+b.body.length]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact spec.facts.term bi b sourceBlock
  have bound : ranges[bi]!.2-1 < result.ctx.insts.size := by
    have limit := (Array.getElem?_eq_some_iff.mp placeholder).1
    rw [range]; dsimp only; omega
  obtain ⟨jumpTarget,targets,back⟩ := core_jump term prepared bound lowered
  obtain ⟨sourceTarget,target,_,row,_⟩ := stock_lower_jump_successor run node sourceBlock term
  have targetBang : result.order.successors[label]! = #[target] := by rw [getElem!_def,row]
  rw [targetBang] at targets
  have same : target = jumpTarget := by simpa using targets
  subst jumpTarget
  refine ⟨target,_,placed,?_,row⟩
  simp only [Array.back?_map,suffix,Array.back?_append,back,Option.some_or,Option.map_some]
  rfl

end Backend.Stock.Proof
