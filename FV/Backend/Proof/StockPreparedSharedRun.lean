import FV.Backend.Proof.StockPreparedSharedJump
import FV.Backend.Proof.StockSharedJump

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgeSpill
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

/-- Shared-target spill execution for an arbitrary actual prepared incoming
edge. The exact jump, selected index0, singleton successors and last instruction
placement follow from actual Stock/preparation/CFG facts. Original theorem
variants remain available. Availability remains an internal dataflow obligation. -/
theorem stock_spill_prepared_shared_jump_runs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (ssa : (valueDefs f).Nodup)
    {p : EdgeVCode} (raw : prepareAt result.code result.edgeArgs = .ok p)
    {c : CheckCtx} (code : c.vc = p.code) (allocated : c.rf = spillAllocAt p.code p.edges)
    {preds : Array (Array Nat)} (cfg : p.code.cfg = .ok (c.succs,preds)) {post body : Nat → Nat → Bool}
    {b target j : Nat} {vb tb : VBlock} {successors : Array Nat} {row : Array (Array Reg)} {args : Array Reg}
    (notEntry : target ≠ 0) (source : p.code.blocks[b]? = some vb) (targetBlock : p.code.blocks[target]? = some tb)
    (atSuccessors : c.succs[b]? = some successors) (edge : successors[j]? = some target)
    (shared : 1 < (preds[target]?.getD #[]).size)
    (atRow : p.edges[b]? = some row) (atArgs : row[0]? = some args)
    {A : Nat → Bool} (availability : EntryAvailAt p.code vb 0 args tb A (body target))
    {a : AState} (good : GoodAt p.code p.edges A a) :
    Spill.Runs c vb (vb.insts.size-1)
      (jumpCopies p.code p.edges c.succs preds b ++
        spillInstAt (spillHomesAt p.code p.edges) (vb.insts.size-1) (.jump p.code.blocks[target]!.label)) a
      (fun k' out => k' = vb.insts.size ∧ ∃ e,EdgeTransferAt c p.edges b target 0 args tb out e ∧
        GoodAt p.code p.edges (body target) e ∧
        (preEntryStateAt p.code p.edges c.succs preds post body target).le e = true) := by
  obtain ⟨actual,atActual,back,single,zero⟩ := stock_prepare_shared_jump_cfg run scope raw cfg atSuccessors edge (by
    cases atPred : preds[target]? with
    | none => simp [atPred] at shared
    | some ps => simpa only [getElem!_def,atPred,Option.getD_some] using shared)
  rw [source] at atActual
  cases atActual
  have instruction : vb.insts[vb.insts.size-1]? = some (.jump p.code.blocks[target]!.label) := by
    simpa only [Array.back?_eq_getElem?] using back
  have nonempty : 0 < vb.insts.size := by
    have bound := (Array.getElem?_eq_some_iff.mp instruction).1
    omega
  have execution := stock_spill_shared_jump_runs run scope ssa raw code allocated cfg (post := post) (body := body) notEntry source targetBlock
    single shared atRow atArgs back instruction availability good
  exact execution.mono (fun k' out result => ⟨by have := result.1; omega,result.2⟩)

end Backend.Stock.Proof
