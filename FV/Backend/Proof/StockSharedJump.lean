import FV.Backend.Proof.PerEdgeSpillSharedJump
import FV.Backend.Proof.StockPreEntryState

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original Stock scope/SSA derive shared-copy arity, classes, distinctness and
storage. Real copy/jump/edge execution establishes successor GoodAt and the
canonical checker pre-entry inclusion; no additional source check is added. -/
theorem stock_spill_shared_jump_runs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {p : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok p)
    {c : CheckCtx} (code : c.vc = p.code) (allocated : c.rf = spillAllocAt p.code p.edges)
    {preds : Array (Array Nat)} (cfg : p.code.cfg = .ok (c.succs,preds)) {post body : Nat → Nat → Bool}
    {b target k : Nat} {vb tb : VBlock} {label : Label} {row : Array (Array Reg)} {args : Array Reg}
    (notEntry : target ≠ 0) (source : p.code.blocks[b]? = some vb) (targetBlock : p.code.blocks[target]? = some tb)
    (successors : c.succs[b]? = some #[target]) (shared : 1 < (preds[target]?.getD #[]).size)
    (atRow : p.edges[b]? = some row) (atArgs : row[0]? = some args)
    (atLast : vb.insts.back? = some (.jump label)) (instruction : vb.insts[k]? = some (.jump label))
    {A : Nat → Bool} (availability : EntryAvailAt p.code vb 0 args tb A (body target))
    {a : AState} (good : GoodAt p.code p.edges A a) :
    Spill.Runs c vb k (jumpCopies p.code p.edges c.succs preds b ++ spillInstAt (spillHomesAt p.code p.edges) k (.jump label)) a
      (fun k' out => k' = k+1 ∧ ∃ e,EdgeTransferAt c p.edges b target 0 args tb out e ∧
        GoodAt p.code p.edges (body target) e ∧
        (preEntryStateAt p.code p.edges c.succs preds post body target).le e = true) := by
  obtain ⟨prepared,raw',_,_,arguments,parameters⟩ := stock_prepare_copy_metadata run scope ssa
  have same := Except.ok.inj (raw.symm.trans raw')
  subst prepared
  have arity := stock_prepare_edge_arity run scope ssa raw c.succs preds cfg b 0 target #[target] row args tb
    successors (by rfl) atRow atArgs targetBlock
  have slots : c.rf.spillSlots = (spillHomesAt p.code p.edges).size + maxArgsAt p.edges := by
    rw [allocated]; exact (spillAllocAt_storage _ _).1
  exact spill_shared_jump_runs code slots notEntry source targetBlock successors shared atRow atArgs arity
    (arguments b 0 row args atRow atArgs) (parameters target tb targetBlock) atLast instruction availability good

end Backend.Stock.Proof
