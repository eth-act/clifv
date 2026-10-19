import FV.Backend.Lowering.StockD0
import Lean
namespace Backend.Stock.D0
set_option maxRecDepth 20000
set_option maxHeartbeats 30000
set_option Elab.async false
attribute [local irreducible] emitBranch collectOutgoing scanBlock Isle.Aarch64.program
private theorem collect_empty (ctx : Ctx) (order : Order) (bi : Nat) (input : State) :
    collectOutgoing ctx order bi #[] input = .ok (input, #[]) := by
  unfold collectOutgoing
  rfl
#print axioms collect_empty
/-- Zero outgoing vectors follow from the real collector for zero targets,
without evaluating the ISLE scan or importing unrelated rule-family proofs. -/
private theorem core_empty_outgoing {ctx : Ctx} {order : Order} {f : Clif.Function}
    {b : Clif.Block} {bi start stop : Nat} {data : Backend.V}
    {input : State} {output : LoweredBlockCore} {values : List Nat}
    (term : b.term = .ret values)
    (run : lowerBlockCore ctx order f b bi start stop data #[] input = .ok output) :
    output.outgoing = #[] := by
  simp only [lowerBlockCore, term, Bool.false_eq_true, ↓reduceIte,
    collect_empty, bind, Except.bind, pure, Except.pure] at run
  repeat' first | (solve | cases run) | split at run
  all_goals cases run; rfl
#print axioms core_empty_outgoing


private theorem source_order (name : String) (c : Configuration) (runs : List Clif.RunCommand) :
    blockOrder (source name c runs) =
      .ok {nodes := #[.original 0], successors := #[#[]]} := by
  cases c <;> cbv
#print axioms source_order

attribute [local irreducible] lowerBlockCore assembleOriginalBlock termData abiTerm tryCallData recordCore

private theorem only_node : #[Node.original 0][0]! = .original 0 := by decide +kernel
private theorem only_targets : (#[(#[] : Array Nat)])[0]! = #[] := by decide +kernel

private theorem node_empty_outgoing {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {f : Clif.Function} {paramBytes : List Nat} {input output : DriverState}
    {values : List Nat} (term : (f.blocks[0]!).term = .ret values)
    (run : lowerNode ctx ranges
      {nodes := #[.original 0], successors := #[#[]]} f paramBytes 0 input = .ok output) :
    output.edgeArgs = input.edgeArgs.set! 0 #[] := by
  unfold lowerNode at run
  dsimp only at run
  simp only [only_node, only_targets, term] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  all_goals
    cases run
    exact congrArg (input.edgeArgs.set! 0) (core_empty_outgoing term (by assumption))

#print axioms node_empty_outgoing

private theorem source_term (name : String) (c : Configuration) (runs : List Clif.RunCommand) :
    ((source name c runs).blocks[0]!).term = .ret [0] := by
  cases c <;> cbv

private theorem only_traversal
    (step : DriverState → Nat → Except String DriverState) (input : DriverState) :
    (Array.range 1).reverse.toList.foldlM step input = step input 0 := by
  cbv
  cases step input 0 <;> rfl

private theorem empty_edges_map (resolve : Reg → Reg) :
    ((Array.replicate 1 (#[] : Array (Array Reg))).set! 0 #[]).map
      (fun args => args.map fun rs => rs.map resolve) = #[#[]] := by cbv

attribute [local irreducible] buildCtx lowerNode

/-- The actual successful Stock traversal carries no successor arguments on D0;
this establishes the structural dispatcher guard before any projection to VCode. -/
theorem stock_edges_empty (name : String) (c : Configuration) (runs : List Clif.RunCommand)
    {result : Result} (run : Stock.lower (source name c runs) = .ok result) :
    result.edgeArgs = #[#[]] := by
  simp only [Stock.lower, source_order, Array.size_singleton, only_traversal] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure, Array.size_singleton, only_traversal] at run
    | split at run
  all_goals
    cases run
    have edges := node_empty_outgoing (source_term name c runs) (by assumption)
    simp only [edges]
    exact empty_edges_map _

#print axioms stock_edges_empty
end Backend.Stock.D0

