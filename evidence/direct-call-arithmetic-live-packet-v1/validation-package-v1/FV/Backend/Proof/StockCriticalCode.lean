import FV.Backend.Proof.StockOrderGraph

/-! Actual synthetic-node branch collection and returned VCode placement.
The whole traversal and final resolver determine the installed code. -/
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


private theorem node_edge_assembled {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label pred k target : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (node : order.nodes[label]! = .edge pred k target) :
    ∃ args next,branchArgs ctx input.state pred k = .ok (args,next) ∧
      output.blocks = input.blocks.set! label {label,insts := #[.jump order.successors[label]![0]!],branchArgs := args} := by
  unfold lowerNode at run
  simp only [node] at run
  cases call : branchArgs ctx input.state pred k with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨args,next⟩ := pair
    simp only [call,bind,Except.bind,pure,Except.pure] at run
    refine ⟨args,next,rfl,?_⟩
    cases run
    rfl

/-- Every actual synthetic edge node is present in returned VCode, with its
real collected arguments after final resolution and exactly its graph jump.
The collection run and block placement are derived from whole lowering. -/
theorem stock_lower_critical_code {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {label pred k target : Nat}
    (tag : result.order.nodes[label]? = some (.edge pred k target)) :
    ∃ (input next : State) (args : Array Reg) (targetLabel : Nat),
      branchArgs result.ctx input pred k = .ok (args,next) ∧
      result.order.successors[label]? = some #[targetLabel] ∧
      result.order.nodes[targetLabel]? = some (.original target) ∧
      result.code.blocks[label]? = some {label,insts := #[.jump targetLabel],branchArgs := args.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))} := by
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
      have node : result.order.nodes[label]! = .edge pred k target := by
        simp only [getElem!_def,tag,Option.getD_some]
      obtain ⟨args,next,call,installed⟩ := node_edge_assembled step node
      have beforeBound : label < before.blocks.size := by
        rw [nodes_size first]
        simpa only [startDriver,Array.size_replicate] using bound
      let block : VBlock := {label,insts := #[.jump result.order.successors[label]![0]!],branchArgs := args}
      have afterBlock : after.blocks[label]? = some block := by
        rw [installed,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt beforeBound]
      have finalBlock : driver.blocks[label]? = some block := by
        rw [nodes_frame folded,afterBlock]
        intro k member
        rw [(stock_backward_suffix_split parts).2] at member
        have small : k < label := by simpa using member
        omega
      obtain ⟨targetLabel,successors,targetTag⟩ := stock_lower_edge_successor run tag
      have destination : result.order.successors[label]![0]! = targetLabel := by
        simp [getElem!_def,successors]
      refine ⟨before.state,next,args,targetLabel,call,successors,targetTag,?_⟩
      simp only [blocks,Array.getElem?_map,finalBlock,Option.map_some]
      simp [block,destination,MInst.mapRegs]
end Backend.Stock.Proof
