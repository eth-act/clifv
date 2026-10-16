import FV.Backend.Proof.PerEdgeSpillEntryGood
import FV.Backend.Proof.PerEdgeSpillTerminalBlock

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual Stock successor-entry availability from predecessor execution.
Original source conditions derive copy metadata/storage; remaining syntactic
static/class/dataflow facts are internal proof obligations, not input filters. -/
theorem stock_spill_entry_good_runs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {p : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok p)
    {c : CheckCtx} (code : c.vc = p.code) (allocated : c.rf = spillAllocAt p.code p.edges)
    {preds : Array (Array Nat)} (cfg : p.code.cfg = .ok (c.succs,preds))
    {b target j : Nat} {ss : Array Nat} {row : Array (Array Reg)} {args : Array Reg} {vb tb : VBlock}
    (source : p.code.blocks[b]? = some vb) (targetBlock : p.code.blocks[target]? = some tb)
    (successors : c.succs[b]? = some ss) (edge : ss[j]? = some target) (pred : preds[target]? = some #[b])
    (atRow : p.edges[b]? = some row) (atArgs : row[j]? = some args)
    {T : MInst} {ops : Array Operand} (atLast : vb.insts.back? = some T) (operands : T.operands = .ok ops)
    (static : OpsOk ops T.clobbers) {A wanted : Nat → Bool}
    (availability : EntryAvailAt p.code vb j args tb (availInst T A) wanted)
    {out : AState} (good : GoodAt p.code p.edges (availInst T A) out)
    (kept : ∀ x ∈ termEdgeDefs vb j,Sym.vreg x.1.vreg ∈ out.get x.2) :
    ∃ e,EdgeTransferAt c p.edges b target j args tb out e ∧
      Spill.Runs c tb 0 (spillEntryStoresAt (spillHomesAt p.code p.edges) p.code c.succs preds target ++
        spillEntryCopiesAt (spillHomesAt p.code p.edges) p.code p.edges c.succs preds target) e
        (fun k final => k = 0 ∧ GoodAt p.code p.edges wanted final) := by
  obtain ⟨prepared,raw',_,_,arguments,parameters⟩ := stock_prepare_copy_metadata run scope ssa
  have same := Except.ok.inj (raw.symm.trans raw')
  subst prepared
  have arity := stock_prepare_edge_arity run scope ssa raw c.succs preds cfg b j target ss row args tb
    successors edge atRow atArgs targetBlock
  have slots : c.rf.spillSlots = (spillHomesAt p.code p.edges).size + maxArgsAt p.edges := by
    rw [allocated]; exact (spillAllocAt_storage _ _).1
  exact spill_entry_good_runs code slots cfg source targetBlock successors edge pred atRow atArgs arity
    (arguments b j row args atRow atArgs) (parameters target tb targetBlock) atLast operands static availability good kept

/-- A complete actual return successor checks from its actual predecessor edge
state. The entry proof is derived above, then the real allocated block runs
through result stores/copies, restores, operand loads and its return. -/
theorem stock_spill_return_successor_runs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {p : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok p)
    {c : CheckCtx} (code : c.vc = p.code) (allocated : c.rf = spillAllocAt p.code p.edges)
    {preds : Array (Array Nat)} (cfg : p.code.cfg = .ok (c.succs,preds))
    {b target j : Nat} {ss : Array Nat} {row : Array (Array Reg)} {args : Array Reg} {vb tb : VBlock}
    (source : p.code.blocks[b]? = some vb) (targetBlock : p.code.blocks[target]? = some tb)
    (successors : c.succs[b]? = some ss) (edge : ss[j]? = some target) (pred : preds[target]? = some #[b])
    (atRow : p.edges[b]? = some row) (atArgs : row[j]? = some args)
    {T : MInst} {ops : Array Operand} (atLast : vb.insts.back? = some T) (operands : T.operands = .ok ops)
    (static : OpsOk ops T.clobbers) {A wanted : Nat → Bool}
    (availability : EntryAvailAt p.code vb j args tb (availInst T A) wanted)
    {out : AState} (good : GoodAt p.code p.edges (availInst T A) out)
    (kept : ∀ x ∈ termEdgeDefs vb j,Sym.vreg x.1.vreg ∈ out.get x.2)
    {us : List (Reg × Reg)} (notEntry : target ≠ 0) (instructions : tb.insts = #[.rets us])
    (retStatic : SpillInstOk (.rets us))
    (retClasses : ∀ os,(MInst.rets us).operands = .ok os → ∀ o ∈ os.toList,p.code.classes[o.vreg]? = some o.cls)
    (retUses : ∀ os,(MInst.rets us).operands = .ok os → ∀ o ∈ os.toList,o.kind = .use → wanted o.vreg = true) :
    ∃ e final,EdgeTransferAt c p.edges b target j args tb out e ∧
      c.runBlock target e = .ok final ∧ GoodAt p.code p.edges (availInst (.rets us) wanted) final ∧
      (bodyStateAt p.code p.edges (availInst (.rets us) wanted)).le final = true := by
  obtain ⟨e,transfer,entry⟩ := stock_spill_entry_good_runs run scope ssa raw code allocated cfg source targetBlock successors edge pred
    atRow atArgs atLast operands static availability good kept
  obtain ⟨final,checked,good,least⟩ := spill_return_block_after_entry code allocated cfg targetBlock notEntry instructions
    retStatic retClasses retUses entry
  exact ⟨e,final,transfer,checked,good,least⟩

end Backend.Stock.Proof
