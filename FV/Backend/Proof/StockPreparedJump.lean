import FV.Backend.Proof.StockSharedJumpCfg
import FV.Backend.Proof.PerEdgePrepareJump
import FV.Backend.Proof.StockPreparedArity

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.PerEdgePrep
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Original Stock scope supplies the actual preparation domain. Every live
emitted jump retains its instruction kind/count and parameters at the real
prepared counterpart, including original and critical source blocks. -/
theorem stock_prepare_jump_counterpart {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {p : EdgeVCode}
    (raw : prepareAt result.code result.edgeArgs = .ok p)
    {ss0 ps0 : Array (Array Nat)} (cfg0 : result.code.cfg = .ok (ss0,ps0))
    {b : Nat} {vb : VBlock} {old : Label} (sourceBlock : result.code.blocks[b]? = some vb)
    (live : Prep.mk (reachable ss0) b) (back : vb.insts.back? = some (.jump old)) :
    ∃ (ss3 ps3 : Array (Array Nat)) (q : Nat) (vb' : VBlock) (label : Label),
      p.code.cfg = .ok (ss3,ps3) ∧ sigmaOf result.code p.code b = some q ∧ p.code.blocks[q]? = some vb' ∧
      vb'.insts.back? = some (.jump label) ∧ vb'.insts.size = vb.insts.size ∧ vb'.params = vb.params := by
  obtain ⟨nonempty,labels⟩ := stock_prepare_domain run scope
  exact prepareAt_jump_counterpart raw nonempty labels cfg0 sourceBlock live back

/-- Every live predecessor of a shared computed Stock graph target has an
actual prepared jump counterpart. The emitted jump premise is derived from
actual indexed incoming edges, including forced one-successor TryCall routes.
Universal prepared shared-target multiplicity transport remains separate. -/
theorem stock_prepare_shared_jump_counterpart {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) {p : EdgeVCode}
    (raw : prepareAt result.code result.edgeArgs = .ok p)
    {ss0 ps0 : Array (Array Nat)} (cfg0 : result.code.cfg = .ok (ss0,ps0))
    {targetLabel b j b₂ j₂ : Nat} {ss ss₂ : Array Nat}
    (row : result.order.successors[b]? = some ss) (edge : ss[j]? = some targetLabel)
    (otherRow : result.order.successors[b₂]? = some ss₂) (otherEdge : ss₂[j₂]? = some targetLabel)
    (distinct : b ≠ b₂ ∨ j ≠ j₂) (live : Prep.mk (reachable ss0) b) :
    ∃ (ss3 ps3 : Array (Array Nat)) (q : Nat) (vb vb' : VBlock) (label : Label),
      result.code.blocks[b]? = some vb ∧ vb.insts.back? = some (.jump targetLabel) ∧
      p.code.cfg = .ok (ss3,ps3) ∧ sigmaOf result.code p.code b = some q ∧ p.code.blocks[q]? = some vb' ∧
      vb'.insts.back? = some (.jump label) ∧ vb'.insts.size = vb.insts.size ∧ vb'.params = vb.params := by
  obtain ⟨vb,sourceBlock,back,_,_⟩ := stock_lower_shared_jump_cfg run scope row edge otherRow otherEdge distinct
  obtain ⟨ss3,ps3,q,vb',label,cfg3,sigma,atNew,newBack,size,params⟩ :=
    stock_prepare_jump_counterpart run scope raw cfg0 sourceBlock live back
  exact ⟨ss3,ps3,q,vb,vb',label,sourceBlock,back,cfg3,sigma,atNew,newBack,size,params⟩

end Backend.Stock.Proof
