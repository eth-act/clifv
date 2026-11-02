import FV.Backend.Proof.StockEdgeValues
import FV.Backend.Proof.StockBranchArgumentCode

/-! Actual original-node parameter fields after assembly and final resolution.
This connects the computed source-copy relation to returned VCode metadata. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock

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
  simp [Array.getElem?_setIfInBounds,Ne.symm different]

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


private def parameterReg (ctx : Ctx) (q : Nat × Clif.Ty) : Except String Reg :=
  match ctx.valueReg? q.1 with | some r => .ok r | none => .error s!"unknown value v{q.1}"

private theorem assembled_parameters {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (entry : bi ≠ 0)
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    b.params.toArray.mapM (parameterReg ctx) = .ok block.params ∧ block.label = label := by
  have zero : (bi == 0) = false := by simp [entry]
  unfold assembleOriginalBlock at run
  simp only [zero,Bool.false_eq_true,ite_false] at run
  change (do
    let ps ← b.params.toArray.mapM (parameterReg ctx)
    pure ({label := label,insts := code,params := ps,branchArgs := if targets.size == 1 then outgoing[0]! else #[]} : VBlock)) = .ok block at run
  cases mapped : b.params.toArray.mapM (parameterReg ctx) with
  | error e => simp only [mapped,bind,Except.bind] at run; cases run
  | ok ps =>
    simp only [mapped,bind,Except.bind,pure,Except.pure] at run
    cases run
    exact ⟨rfl,rfl⟩

private theorem list_mapM_total {α β : Type} (xs : List α) (f : α → Except String β) (g : α → β)
    (total : ∀ x ∈ xs,f x = .ok (g x)) : xs.mapM f = .ok (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,total x (by simp),ih (fun y h => total y (by simp [h])),
      bind,Except.bind,pure,Except.pure,List.map_cons]

private theorem parameter_total {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) :
    b.params.toArray.mapM (parameterReg result.ctx) =
      .ok ((b.params.map (fun q => Reg.vreg (edgeValueNum result.ctx q.1) .int)).toArray) := by
  obtain ⟨ranges,params,driver,build,ordered,folded,events,final,blocks⟩ := lower_code_origin run
  obtain ⟨original,st,sourceBuild,spec,view⟩ := buildCtx_source build
  have total : ∀ q ∈ b.params,parameterReg result.ctx q = .ok (.vreg (edgeValueNum result.ctx q.1) .int) := by
    intro q member
    have old := (spec.facts.types ssa).2 b (List.mem_of_getElem? block) q member
    have typed : result.ctx.valueType? q.1 = some (CTy.ofClif q.2) := by
      simpa only [Ctx.valueType?,view.valTy] using old
    obtain ⟨key,mapped⟩ := (buildCtx_mappedInv scope build).typedReg q.1 _ typed
    simp only [parameterReg,edgeValueNum,mapped]
  rw [Array.mapM_eq_mapM_toList]
  simp only [List.toList_toArray,list_mapM_total _ _ _ total]
  rfl

private theorem node_original_assembled {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label bi : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (node : order.nodes[label]! = .original bi) :
    ∃ (data : Backend.V) (core : LoweredBlockCore) (block : VBlock),
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state = .ok core ∧
      assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
        core.outgoing params core.state.uses core.code = .ok block ∧
      output.blocks = input.blocks.set! label block := by
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
          exact ⟨data,core,block,coreRun,assembled,rfl⟩

private theorem original_block_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat}
    (tag : result.order.nodes[label]? = some (.original bi)) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (input : State) (data : Backend.V)
      (core : LoweredBlockCore) (block : VBlock),
      lowerBlockCore result.ctx result.order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data result.order.successors[label]! input = .ok core ∧
      assembleOriginalBlock result.ctx f f.blocks[bi]! bi label result.order.successors[label]!
        core.outgoing params core.state.uses core.code = .ok block ∧
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
        simp only [getElem!_def,tag,Option.getD_some]
      obtain ⟨data,core,block,coreRun,assembled,installed⟩ := node_original_assembled step node
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
      exact ⟨ranges,params,before.state,data,core,block,coreRun,assembled,
        by simp only [blocks,Array.getElem?_map,finalBlock,Option.map_some]⟩

/-- The returned order is the order computed by the actual Stock algorithm. -/
theorem stock_lower_order {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    blockOrder f = .ok result.order := by
  obtain ⟨ranges,params,driver,build,ordered,rest⟩ := lower_code_origin run
  exact ordered

/-- Every actual nonentry original node has its source block's mapped and
finally resolved parameter registers in the returned VCode. Source scope/SSA
derive all mappings; no parameter-map certificate is supplied. -/
theorem stock_lower_original_block_params {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {label bi : Nat} {b : Clif.Block} (tag : result.order.nodes[label]? = some (.original bi))
    (source : f.blocks[bi]? = some b) (entry : bi ≠ 0) :
    ∃ block : VBlock,result.code.blocks[label]? = some block ∧ block.label = label ∧
      block.params = ((edgeParamNumbers result b).map (fun n => Reg.vreg n .int)).toArray := by
  obtain ⟨ranges,params,input,data,core,block,coreRun,assembled,placed⟩ := original_block_origin run tag
  have actual : f.blocks[bi]! = b := by simp only [getElem!_def,source,Option.getD_some]
  rw [actual] at assembled
  obtain ⟨paramRun,labelled⟩ := assembled_parameters entry assembled
  have parameters := Except.ok.inj (paramRun.symm.trans (parameter_total run scope ssa source))
  refine ⟨_,placed,labelled,?_⟩
  simp [parameters,edgeParamNumbers,List.map_map,Function.comp_def,resolve_vreg,aliasNum]

private theorem assembled_arguments {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    block.branchArgs = (if targets.size == 1 then outgoing[0]! else #[]) ∧ block.label = label := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; constructor <;> simp_all

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

private theorem outgoing_one {ctx : Ctx} {order : Order} {bi label target : Nat}
    {input next : State} {outgoing : Array (Array Reg)} (node : order.nodes[label]! = .original target)
    (run : collectOutgoing ctx order bi #[label] input = .ok (next,outgoing)) :
    ∃ args after,branchArgs ctx input bi 0 = .ok (args,after) ∧ outgoing = #[args] := by
  unfold collectOutgoing at run
  change ([(label,0)] : List (Nat × Nat)).foldlM (outgoingStep ctx order bi) (input,#[]) = .ok (next,outgoing) at run
  simp only [List.foldlM_cons,List.foldlM_nil] at run
  unfold outgoingStep at run
  simp only [node] at run
  cases call : branchArgs ctx input bi 0 with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨args,after⟩ := pair
    simp only [call,bind,Except.bind,pure,Except.pure] at run
    refine ⟨args,after,rfl,?_⟩
    cases run
    rfl

/-- The actual original jump block carries its resolved source argument list.
The actual successor node/edge shape identifies a direct original successor;
all collection/helper calls are derived from the successful whole driver. -/
theorem stock_lower_original_jump_args {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {label bi targetLabel targetBi : Nat} {b : Clif.Block} {bc : Clif.BlockCall}
    (tag : result.order.nodes[label]? = some (.original bi)) (source : f.blocks[bi]? = some b)
    (term : b.term = .jump bc) (successors : result.order.successors[label]! = #[targetLabel])
    (target : result.order.nodes[targetLabel]? = some (.original targetBi)) :
    ∃ block : VBlock,result.code.blocks[label]? = some block ∧ block.label = label ∧
      block.branchArgs = ((edgeArgumentNumbers result bc).map (fun n => Reg.vreg n .int)).toArray := by
  obtain ⟨ranges,params,input,data,core,block,coreRun,assembled,placed⟩ := original_block_origin run tag
  have actual : f.blocks[bi]! = b := by simp only [getElem!_def,source,Option.getD_some]
  rw [actual,successors] at coreRun assembled
  obtain ⟨before,after,outgoing⟩ := core_outgoing coreRun
  have node : result.order.nodes[targetLabel]! = .original targetBi := by
    simp only [getElem!_def,target,Option.getD_some]
  obtain ⟨args,next,call,vector⟩ := outgoing_one node outgoing
  have numbers := stock_branchArgs_jump_numbers run scope source term call
  obtain ⟨arguments,labelled⟩ := assembled_arguments assembled
  have raw : block.branchArgs = args := by simpa [vector, getElem!_def] using arguments
  refine ⟨_,placed,labelled,?_⟩
  simpa only [raw] using numbers
end Backend.Stock.Proof
