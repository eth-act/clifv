module

public import FV.Backend.Proof.PerEdgePreparedArity
public import FV.Backend.Proof.StockSpillCopyMetadata

@[expose] public section

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Every actual prepared Stock edge has its target's exact parameter count,
under the original scope/SSA assumptions. Neither input nor output edge arity
is supplied by the caller. -/
theorem stock_prepare_edge_arity {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {prepared : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok prepared) :
    ∀ (ss ps : Array (Array Nat)),prepared.code.cfg = .ok (ss,ps) →
      EdgeArityAt prepared.code prepared.edges ss := by
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  obtain ⟨_,ss0,ps0,cfg0,_⟩ := PerEdgePrep.prepareAt_input_facts raw
  intro ss ps cfg
  exact PerEdgePrep.prepareAt_edge_arity raw nonempty labels cfg0
    (stock_lower_edge_arity run scope ssa ss0 ps0 cfg0) cfg

/-- Actual Stock/prepared selected-edge spill copies derive arity as well as
classes, parameter distinctness, storage bounds and the before-terminator check.
The older theorem accepting an internal arity premise remains unchanged. -/
theorem stock_spillArgMovesAt_edge_runs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {prepared : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok prepared)
    {c : CheckCtx} (allocated : c.rf = spillAllocAt prepared.code prepared.edges)
    {ss ps : Array (Array Nat)} (cfg : prepared.code.cfg = .ok (ss,ps))
    {b j target execution : Nat} {succs : Array Nat} {row : PerEdgePrep.EdgeRow}
    {args : Array Reg} {vb tb : VBlock}
    (atSuccs : ss[b]? = some succs) (edge : succs[j]? = some target)
    (atRow : prepared.edges[b]? = some row) (atArgs : row[j]? = some args)
    (atTarget : prepared.code.blocks[target]? = some tb) (atExecution : prepared.code.blocks[execution]? = some vb)
    {a0 : AState} (stateSize : a0.size = stateSizeAt prepared.code prepared.edges) :
    Runs c vb 0 (spillArgMovesAt (spillHomesAt prepared.code prepared.edges) args tb.params) a0
      (SpillCopyPost prepared args tb a0) := by
  have arity := stock_prepare_edge_arity run scope ssa raw ss ps cfg b j target succs row args tb
    atSuccs edge atRow atArgs atTarget
  exact stock_spillArgMovesAt_runs run scope ssa raw allocated atRow atArgs atTarget atExecution arity stateSize

end Backend.Stock.Proof
