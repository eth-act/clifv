import FV.Backend.Proof.StockEntryCode

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Stock.runTerm lowerBlockCore assembleOriginalBlock branchArgs emitBranch collectOutgoing scanBlock

private theorem node_install {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∃ block,output.blocks = input.blocks.set! label block := by
  unfold lowerNode at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; exact ⟨_,rfl⟩

private theorem nodes_size {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    output.blocks.size = input.blocks.size := by
  induction labels generalizing input with
  | nil => cases run;rfl
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,step,rest⟩ := Except.bind_ok run
    obtain ⟨block,installed⟩ := node_install step
    rw [ih rest,installed]
    simp

private def startDriver (initial : State) (n : Nat) : DriverState := {
  state := initial,blocks := Array.replicate n default,edgeArgs := Array.replicate n #[],
  schedule := #[],scans := #[],blockScans := #[],rules := #[] }

private theorem origin {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (driver : DriverState),
      blockOrder f = .ok result.order ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d)
        (startDriver result.initial result.order.nodes.size) = .ok driver ∧
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
  exact ⟨_,_,_,by assumption,by assumption,rfl⟩

/-- Actual traversal and final aliases preserve the original allocated block count. -/
theorem stock_lower_code_block_count {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) :
    blockOrder f = .ok result.order ∧ result.code.blocks.size = result.order.nodes.size := by
  obtain ⟨ranges,params,driver,ordered,folded,blocks⟩ := origin run
  refine ⟨ordered,?_⟩
  rw [blocks,Array.size_map,nodes_size folded]
  exact Array.size_replicate ..

end Backend.Stock.Proof.Acquire810
