import FV.Backend.Proof.StockEntryGood
import FV.Backend.Proof.PerEdgeSpillPreState

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual Stock unique-predecessor entry moves run from a finite canonical
checker input. Original scope and SSA derive all copy shape, arity and storage
metadata; syntactic availability remains an internal dataflow obligation. -/
theorem stock_preEntryStateAt_unique_runs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {p : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok p)
    {succs preds : Array (Array Nat)} (cfg : p.code.cfg = .ok (succs,preds))
    {post body : Nat → Nat → Bool} {b target j : Nat} {ss : Array Nat}
    {row : Array (Array Reg)} {args : Array Reg} {vb tb : VBlock}
    (notEntry : target ≠ 0) (source : p.code.blocks[b]? = some vb) (targetBlock : p.code.blocks[target]? = some tb)
    (successors : succs[b]? = some ss) (edge : ss[j]? = some target) (pred : preds[target]? = some #[b])
    (atRow : p.edges[b]? = some row) (atArgs : row[j]? = some args)
    {T : MInst} {ops : Array Operand} (atLast : vb.insts.back? = some T) (operands : T.operands = .ok ops)
    (static : OpsOk ops T.clobbers) {A : Nat → Bool} (postAt : post b = availInst T A)
    (availability : EntryAvailAt p.code vb j args tb (post b) (body target)) :
    Spill.Runs (spillCtxAt p.code p.edges succs) tb 0
      (spillEntryStoresAt (spillHomesAt p.code p.edges) p.code succs preds target ++
       spillEntryCopiesAt (spillHomesAt p.code p.edges) p.code p.edges succs preds target)
      (preEntryStateAt p.code p.edges succs preds post body target)
      (fun k final => k = 0 ∧ GoodAt p.code p.edges (body target) final ∧
        (bodyStateAt p.code p.edges (body target)).le final = true) := by
  obtain ⟨prepared,raw',_,_,arguments,parameters⟩ := stock_prepare_copy_metadata run scope ssa
  have same := Except.ok.inj (raw.symm.trans raw')
  subst prepared
  have arity := stock_prepare_edge_arity run scope ssa raw succs preds cfg b j target ss row args tb
    successors edge atRow atArgs targetBlock
  exact preEntryStateAt_unique_runs cfg notEntry source targetBlock successors edge pred atRow atArgs arity
    (arguments b j row args atRow atArgs) (parameters target tb targetBlock) atLast operands static postAt availability

end Backend.Stock.Proof
