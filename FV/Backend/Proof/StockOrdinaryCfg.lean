import FV.Backend.Proof.StockEmittedGraph
import FV.Backend.Proof.StockGraphBounds
import FV.Backend.Proof.StockControlShape
import FV.Backend.Proof.StockNamedBranchTargets

namespace Backend.Stock.Proof.OrdinaryCfg
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock

/-- The unchanged ordinary branch forms; this classifies internal proof cases. -/
def ordinary : Clif.Terminator → Bool
  | .jump .. | .brif .. | .brTable .. => true
  | _ => false

private theorem named_targets {ctx : Ctx} {f : Clif.Function} {t : Clif.Terminator}
    {ti : Nat} {data : V} {labels : List Label} {before next : State} {out : V} {trace : List RuleId}
    (prepared : Coverage.blockData f t = .ok data) (ord : ordinary t = true)
    (slot : ctx.insts[ti]? = some ⟨data,[],[],none⟩)
    (run : Stock.runTerm ctx "lower_branch" [.inst ti,.labels labels] before = .ok (some out,next,trace)) :
    ∃ last,next.base.emitted.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels := by
  cases t <;> simp only [ordinary] at ord
  all_goals try contradiction
  all_goals
    simp only [Coverage.blockData,abiTerm] at prepared
    simp only [termData_jump,termData_brif,termData_brTable] at prepared
    cases prepared
  · obtain ⟨label,labelsEq,state,_,_⟩ := Control.stock_named_jump_shape slot run
    exact ⟨.jump label,by rw [state]; simp [LState.emit],rfl,by rw [labelsEq]; rfl⟩
  · exact NamedBranchTargets.stock_named_brif_targets slot run
  · exact NamedBranchTargets.stock_named_table_targets slot run

private theorem branch_targets {ctx : Ctx} {f : Clif.Function} {t : Clif.Terminator}
    {bi ti : Nat} {data : V} {labels : Array Nat} {input : State} {out : BranchEmission}
    (prepared : Coverage.blockData f t = .ok data) (ord : ordinary t = true)
    (slot : ctx.insts[ti]? = some ⟨data,[],[],none⟩)
    (run : emitBranch ctx f t bi ti labels input = .ok out) :
    ∃ last,out.code.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels.toList := by
  let before : State := {input with current := some ti,color := none,base.emitted := #[]}
  unfold emitBranch at run
  change (do
    let (v,next,fired) ← Stock.runTerm ctx "lower_branch" [.inst ti,.labels labels.toList] before
    if v.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t labels next.base.emitted
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
      have code : branchCode f t labels next.base.emitted = .ok next.base.emitted := by
        cases t <;> simp only [ordinary] at ord
        all_goals try contradiction
        all_goals rfl
      simp only [code,bind,Except.bind,pure,Except.pure] at run
      cases run
      exact named_targets prepared ord slot call

private theorem map_some_inv {α : Type} {call : Except String α} {out : Option α}
    (run : (some <$> call) = .ok out) : ∃ value,call = .ok value ∧ out = some value := by
  cases call with
  | error err => cases run
  | ok value => cases run; exact ⟨value,rfl,rfl⟩

private theorem append_last {α : Type} {left right : Array α} {last : α}
    (atLast : right.back? = some last) : (left ++ right).back? = some last := by
  rw [Array.back?_append]
  simp only [atLast]
  rfl

private theorem core_targets {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : V} {labels : Array Nat}
    {input : State} {out : LoweredBlockCore}
    (prepared : Coverage.blockData f b.term = .ok data) (ord : ordinary b.term = true)
    (bound : stop-1 < ctx.insts.size)
    (run : lowerBlockCore ctx order f b bi start stop data labels input = .ok out) :
    ∃ last,out.code.back? = some last ∧ last.isTerminator = true ∧ last.targets = labels.toList := by
  have slot : ({ctx with
      insts := ctx.insts.set! (stop-1) ⟨data,[],[],none⟩
      tryRegs := input.tryRegs[stop-1]! } : Ctx).insts[stop-1]? = some ⟨data,[],[],none⟩ := by
    simp only [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound]
  cases term : b.term <;> simp only [term,ordinary] at ord
  all_goals try contradiction
  all_goals
    unfold lowerBlockCore at run
    simp only [term] at run
    repeat' first
      | (solve | cases run)
      | simp only [bind,Except.bind,pure,Except.pure,Functor.map,Except.map] at run
      | split at run
    all_goals
      cases run
      rename_i _ branch branchRun _ outgoing outgoingRun _ scan scanRun
      obtain ⟨emission,emitted,wrapped⟩ := map_some_inv branchRun
      subst branch
      have prepared' := prepared
      rw [term] at prepared'
      obtain ⟨last,back,ends,targets⟩ := branch_targets prepared' rfl slot emitted
      exact ⟨last,append_last back,ends,targets⟩

private theorem node_install {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ block, output.blocks = input.blocks.set! label block := by
  unfold lowerNode at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  all_goals
    cases run
    exact ⟨_,rfl⟩

private theorem node_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    output.blocks.size = input.blocks.size := by
  obtain ⟨block,installed⟩ := node_install run
  rw [installed]
  simp

private theorem node_frame {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label other : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) (different : other ≠ label) :
    output.blocks[other]? = input.blocks[other]? := by
  obtain ⟨block,installed⟩ := node_install run
  rw [installed]
  simp [Ne.symm different]

private theorem nodes_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    output.blocks.size = input.blocks.size := by
  induction labels generalizing input with
  | nil => cases run; rfl
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [call,bind,Except.bind] at run
      exact (ih run).trans (node_size call)

private theorem nodes_frame {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {other : Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output)
    (different : ∀ k ∈ labels,other ≠ k) : output.blocks[other]? = input.blocks[other]? := by
  induction labels generalizing input with
  | nil => cases run; rfl
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call,bind,Except.bind] at run; cases run
    | ok middle =>
      simp only [call,bind,Except.bind] at run
      exact (ih run (fun k member => different k (List.mem_cons_of_mem _ member))).trans
        (node_frame call (different label (by simp)))

private def startDriver (initial : State) (n : Nat) : DriverState := {
  state := initial,blocks := Array.replicate n default,edgeArgs := Array.replicate n #[],
  schedule := #[],scans := #[],blockScans := #[],rules := #[] }

private theorem lower_code_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (driver : DriverState),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      blockOrder f = .ok result.order ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d)
        (startDriver result.initial result.order.nodes.size) = .ok driver ∧
      result.blockScans = driver.blockScans ∧ result.final = driver.state ∧
      result.code.blocks = driver.blocks.map (fun b => {b with
        insts := b.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := b.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := b.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))}) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,_,_,by assumption,by assumption,by assumption,rfl,rfl,rfl⟩


private theorem node_original_assembled {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label bi : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (node : order.nodes[label]! = .original bi) :
    ∃ (data : Backend.V) (core : LoweredBlockCore) (block : VBlock),
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state = .ok core ∧
      assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
        core.outgoing params core.state.uses core.code = .ok block ∧
      output.blocks = input.blocks.set! label block ∧ Coverage.blockData f f.blocks[bi]!.term = .ok data := by
  let fetchData : Except String Backend.V := match f.blocks[bi]!.term with
    | .tryCall .. | .tryCallIndirect .. => tryCallData f f.blocks[bi]!.term
    | _ => termData (abiTerm f f.blocks[bi]!.term)
  let reject : Bool := (match f.blocks[bi]!.term with | .ret .. => true | _ => false) &&
    (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
  have normal : lowerNode ctx ranges order f params label input = (do
      let data ← fetchData
      if reject then throw "sret parameter is not an entry-block parameter"
      let core ← lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state
      let block ← assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
        core.outgoing params core.state.uses core.code
      pure { recordCore input core bi ranges[bi]!.2 with
        blocks := input.blocks.set! label block,
        edgeArgs := input.edgeArgs.set! label core.outgoing }) := by
    unfold lowerNode
    simp only [node]
    dsimp only [fetchData, reject]
    split <;> simp_all only [reject] <;> rfl
  rw [normal] at run
  cases dataRun : fetchData with
  | error e => simp only [dataRun, bind, Except.bind] at run; cases run
  | ok data =>
    simp only [dataRun, bind, Except.bind] at run
    split at run
    · cases run
    · cases coreRun : lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state with
      | error e => simp only [coreRun] at run; cases run
      | ok core =>
        simp only [coreRun] at run
        cases assembled : assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
          core.outgoing params core.state.uses core.code with
        | error e => simp only [assembled] at run; cases run
        | ok block =>
          simp only [assembled, pure, Except.pure] at run
          cases run
          exact ⟨data,core,block,coreRun,assembled,rfl,dataRun⟩

private theorem original_block_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat}
    (tag : result.order.nodes[label]? = some (.original bi)) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (input : State) (data : Backend.V)
      (core : LoweredBlockCore) (block : VBlock),
      lowerBlockCore result.ctx result.order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data result.order.successors[label]! input = .ok core ∧
      assembleOriginalBlock result.ctx f f.blocks[bi]! bi label result.order.successors[label]!
        core.outgoing params core.state.uses core.code = .ok block ∧
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      Coverage.blockData f f.blocks[bi]!.term = .ok data ∧
      result.code.blocks[label]? = some {block with
        insts := block.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := block.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := block.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))} := by
  obtain ⟨ranges,params,driver,build,ordered,folded,events,final,blocks⟩ := lower_code_origin run
  have bound := (Array.getElem?_eq_some_iff.mp tag).1
  have member : label ∈ (Array.range result.order.nodes.size).reverse.toList := by simpa using bound
  obtain ⟨earlier,suffix,parts,noEarlier⟩ := List.eq_append_cons_of_mem member
  rw [parts,List.foldlM_append] at folded
  cases first : earlier.foldlM (fun d k => lowerNode result.ctx ranges result.order f params k d)
      (startDriver result.initial result.order.nodes.size) with
  | error e => simp only [first,bind,Except.bind] at folded; cases folded
  | ok before =>
    simp only [first,bind,Except.bind] at folded
    rw [List.foldlM_cons] at folded
    cases step : lowerNode result.ctx ranges result.order f params label before with
    | error e => simp only [step,bind,Except.bind] at folded; cases folded
    | ok after =>
      simp only [step,bind,Except.bind] at folded
      have node : result.order.nodes[label]! = .original bi := by
        simp only [getElem!_def,tag]
      obtain ⟨data,core,block,coreRun,assembled,installed,prepared⟩ := node_original_assembled step node
      have beforeBound : label < before.blocks.size := by
        rw [nodes_size first]
        simpa only [startDriver,Array.size_replicate] using bound
      have afterBlock : after.blocks[label]? = some block := by
        rw [installed,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt beforeBound]
      have finalBlock : driver.blocks[label]? = some block := by
        rw [nodes_frame folded,afterBlock]
        intro k member
        rw [(stock_backward_suffix_split parts).2] at member
        have small : k < label := by simpa using member
        omega
      exact ⟨ranges,params,before.state,data,core,block,coreRun,assembled,build,prepared,
        by simp only [blocks,Array.getElem?_map,finalBlock,Option.map_some]⟩

private theorem assemble_suffix {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    ∃ preludeCode : Array MInst, block.insts = preludeCode ++ code := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  all_goals
    cases run
    first | exact ⟨_,rfl⟩ | exact ⟨#[],by simp⟩


private theorem term_map (g : Reg → Reg) (t : MInst) :
    (t.mapRegs g).isTerminator = t.isTerminator := by cases t <;> rfl


/-- Every actual ordinary-branch original node ends in a real terminator whose
targets equal its computed graph row. Source preparation, slot bounds, rule
selection, body prefix, assembly, traversal and final aliasing are all derived
from the original successful driver run. -/
theorem stock_lower_ordinary_targets {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {label bi : Nat}
    (node : result.order.nodes[label]? = some (.original bi))
    (ord : ordinary f.blocks[bi]!.term = true) :
    ∃ (block : VBlock) (last : MInst),result.code.blocks[label]? = some block ∧
      block.insts.back? = some last ∧ last.isTerminator = true ∧
      last.targets = result.order.successors[label]!.toList := by
  obtain ⟨ranges,params,input,data,core,block,lowered,assembled,build,prepared,placed⟩ := original_block_origin run node
  have projected : bi ∈ stockOriginals result.order.nodes := by
    unfold stockOriginals
    exact List.mem_filterMap.mpr ⟨.original bi,Array.mem_toList_iff.mpr (Array.mem_of_getElem? node),rfl⟩
  have biBound := (stock_blockOrder_originals_nodup (stock_lower_order run)
    (fun h => scope.nonempty (List.length_eq_zero_iff.mp h))).2 bi projected
  have sourceBlock : f.blocks[bi]? = some f.blocks[bi] := by simp [biBound]
  obtain ⟨original,oldState,oldBuild,spec,view⟩ := buildCtx_source build
  have range : ranges[bi]! = (blockStart f bi,blockStart f bi+f.blocks[bi].body.length+1) := by
    simp only [getElem!_def,spec.ranges bi f.blocks[bi] sourceBlock]
  have placeholder : result.ctx.insts[blockStart f bi+f.blocks[bi].body.length]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts]
    exact spec.facts.term bi f.blocks[bi] sourceBlock
  have bound : ranges[bi]!.2-1 < result.ctx.insts.size := by
    have limit := (Array.getElem?_eq_some_iff.mp placeholder).1
    rw [range]
    dsimp only
    omega
  obtain ⟨last,back,ends,targets⟩ := core_targets prepared ord bound lowered
  obtain ⟨preludeCode,code⟩ := assemble_suffix assembled
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  refine ⟨_,last.mapRegs resolve,placed,?_,?_,?_⟩
  · simp only [Array.back?_map,code,Array.back?_append,back,Option.some_or,Option.map_some,resolve]
  · simpa only [term_map] using ends
  · simpa only [targets_mapRegs] using targets

/-- Every actual ordinary-branch original node satisfies its complete CFG clause,
including the computed row and the actual emitted target-label lookups. -/
theorem stock_lower_ordinary_cfg {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {label bi : Nat}
    (node : result.order.nodes[label]? = some (.original bi))
    (ord : ordinary f.blocks[bi]!.term = true) :
    ∃ (block : VBlock) (t : MInst) (row : Array Nat),
      result.code.blocks[label]? = some block ∧ block.insts.back? = some t ∧
      t.isTerminator = true ∧ result.order.successors[label]? = some row ∧
      row.size = t.targets.length ∧
      ∀ (j : Nat) (l : Label),t.targets[j]? = some l →
        ∃ k,row[j]? = some k ∧ Prep.lab result.code.blocks l = some k := by
  obtain ⟨block,t,placed,atLast,terminal,targets⟩ := stock_lower_ordinary_targets run scope node ord
  obtain ⟨count,bounds⟩ := stock_lower_graph_bounds run
  have index : label < result.order.successors.size := by
    rw [count]
    exact (Array.getElem?_eq_some_iff.mp placed).1
  let row := result.order.successors[label]
  have atRow : result.order.successors[label]? = some row := Array.getElem?_eq_getElem index
  have rowEq : result.order.successors[label]! = row := by simp only [getElem!_pos result.order.successors label index]; rfl
  rw [rowEq] at targets
  refine ⟨block,t,row,placed,atLast,terminal,atRow,?_,?_⟩
  · rw [targets,Array.length_toList]
  · intro j l atTarget
    rw [targets] at atTarget
    have atValue : row[j]? = some l := by simpa only [Array.getElem?_toList] using atTarget
    have bound := bounds label row atRow l (Array.mem_toList_iff.mpr (Array.mem_of_getElem? atValue))
    exact ⟨l,atValue,Prep.lab_of (stock_prepare_domain run scope).2 bound
      (stock_lower_dense_labels run l bound)⟩


end Backend.Stock.Proof.OrdinaryCfg

namespace Backend.Stock.Proof.OrdinaryCfg
open Backend.Proof Backend.Proof.Driver

/-- Public actual original-node provenance for exact instruction-shape proofs.
The existing original-node traversal, assembly and final resolver are reused;
all prior target-only theorem variants remain unchanged. -/
theorem stock_lower_original_code_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat}
    (tag : result.order.nodes[label]? = some (.original bi)) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (input : State) (data : Backend.V)
      (core : LoweredBlockCore) (block : VBlock) (preludeCode : Array MInst),
      lowerBlockCore result.ctx result.order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data result.order.successors[label]! input = .ok core ∧
      assembleOriginalBlock result.ctx f f.blocks[bi]! bi label result.order.successors[label]!
        core.outgoing params core.state.uses core.code = .ok block ∧
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧
      Coverage.blockData f f.blocks[bi]!.term = .ok data ∧
      result.code.blocks[label]? = some {block with
        insts := block.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
        params := block.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
        branchArgs := block.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))} ∧
      block.insts = preludeCode ++ core.code := by
  obtain ⟨ranges,params,input,data,core,block,lowered,assembled,build,prepared,placed⟩ := original_block_origin run tag
  obtain ⟨preludeCode,suffix⟩ := assemble_suffix assembled
  exact ⟨ranges,params,input,data,core,block,preludeCode,lowered,assembled,build,prepared,placed,suffix⟩

end Backend.Stock.Proof.OrdinaryCfg
