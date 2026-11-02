import FV.Backend.Proof.StockBackwardSuffixSplit
import FV.Backend.Proof.IselExtern

/-! Actual per-successor vectors returned by whole Stock lowering.
Traverse installation/frame facts before applying final alias resolution. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.runTerm lowerBlockCore branchArgs emitBranch collectOutgoing scanBlock

private theorem node_install {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ block, output.edgeArgs = input.edgeArgs.set! label block := by
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
    output.edgeArgs.size = input.edgeArgs.size := by
  obtain ⟨block,installed⟩ := node_install run
  rw [installed]
  simp

private theorem node_frame {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label other : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) (different : other ≠ label) :
    output.edgeArgs[other]? = input.edgeArgs[other]? := by
  obtain ⟨block,installed⟩ := node_install run
  rw [installed]
  simp [Array.getElem?_setIfInBounds,Ne.symm different]

private theorem nodes_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    output.edgeArgs.size = input.edgeArgs.size := by
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
    (different : ∀ k ∈ labels,other ≠ k) : output.edgeArgs[other]? = input.edgeArgs[other]? := by
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
      result.edgeArgs = driver.edgeArgs.map (fun args => args.map (fun rs =>
        rs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,_,_,by assumption,by assumption,by assumption,rfl,rfl,rfl⟩


private theorem node_origin {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label : Nat} (bound : label < result.order.nodes.size) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (input output : DriverState),
      label < input.edgeArgs.size ∧
      lowerNode result.ctx ranges result.order f params label input = .ok output ∧
      result.edgeArgs[label]? = (output.edgeArgs[label]?).map (fun args => args.map (fun rs =>
        rs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) := by
  obtain ⟨ranges,params,driver,build,ordered,folded,events,final,vectors⟩ := lower_code_origin run
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
      have beforeBound : label < before.edgeArgs.size := by
        rw [nodes_size first]
        simpa only [startDriver,Array.size_replicate] using bound
      have finalVector : driver.edgeArgs[label]? = after.edgeArgs[label]? := by
        rw [nodes_frame folded]
        intro k member
        rw [(stock_backward_suffix_split parts).2] at member
        have small : k < label := by simpa using member
        omega
      exact ⟨ranges,params,before,after,beforeBound,step,
        by simp only [vectors,Array.getElem?_map,finalVector]⟩

private theorem node_original_assembled {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label bi : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (node : order.nodes[label]! = .original bi) :
    ∃ (data : Backend.V) (core : LoweredBlockCore) (block : VBlock),
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state = .ok core ∧
      assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
        core.outgoing params core.state.uses core.code = .ok block ∧
      output.edgeArgs = input.edgeArgs.set! label core.outgoing := by
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

/-- Actual original-node outgoing vectors come from its successful core,
with all per-successor vectors retained and finally alias-resolved. This
covers multi-successor branches without using legacy single-vector branchArgs. -/
theorem stock_lower_original_outgoing {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label bi : Nat}
    (tag : result.order.nodes[label]? = some (.original bi)) :
    ∃ (ranges : Array (Nat × Nat)) (input : State) (data : Backend.V) (core : LoweredBlockCore),
      lowerBlockCore result.ctx result.order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data result.order.successors[label]! input = .ok core ∧
      result.edgeArgs[label]? = some (core.outgoing.map (fun args =>
        args.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) := by
  obtain ⟨ranges,params,input,output,bound,nodeRun,stored⟩ := node_origin run (Array.getElem?_eq_some_iff.mp tag).1
  have node : result.order.nodes[label]! = .original bi := by simp [getElem!_def,tag]
  obtain ⟨data,core,block,coreRun,assembled,installed⟩ := node_original_assembled nodeRun node
  rw [installed,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound] at stored
  exact ⟨ranges,input.state,data,core,coreRun,stored⟩

/-- Actual synthetic-node outgoing metadata comes from its successful selected
branchArgs call, retaining the vector through traversal and final resolution. -/
theorem stock_lower_critical_outgoing {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label pred index target : Nat}
    (tag : result.order.nodes[label]? = some (.edge pred index target)) :
    ∃ (input next : State) (args : Array Reg),
      branchArgs result.ctx input pred index = .ok (args,next) ∧
      result.edgeArgs[label]? = some #[args.map
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))] := by
  obtain ⟨ranges,params,input,output,bound,nodeRun,stored⟩ := node_origin run (Array.getElem?_eq_some_iff.mp tag).1
  have node : result.order.nodes[label]! = .edge pred index target := by simp [getElem!_def,tag]
  unfold lowerNode at nodeRun
  simp only [node] at nodeRun
  cases call : branchArgs result.ctx input.state pred index with
  | error e => simp only [call,bind,Except.bind] at nodeRun; cases nodeRun
  | ok pair =>
    obtain ⟨args,next⟩ := pair
    simp only [call,bind,Except.bind,pure,Except.pure] at nodeRun
    cases nodeRun
    dsimp only at stored
    rw [Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt bound] at stored
    exact ⟨input.state,next,args,call,by simpa using stored⟩
end Backend.Stock.Proof
