module

public import FV.Backend.Proof.PerEdgePrepareComplete
public import FV.Backend.Proof.PerEdgePrepareSound

@[expose] public section

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private theorem sameInst_jump {old : Label} {i : MInst} (same : SameInst (.jump old) i) : ∃ label,i = .jump label := by
  rcases same with direct | retarget
  · exact ⟨old,direct⟩
  · cases targets : i.targets with
    | nil => simp [MInst.setTargets,targets] at retarget
    | cons label rest =>
      cases rest with
      | nil =>
        simp only [MInst.setTargets,targets,Option.some.injEq] at retarget
        exact ⟨label,retarget.symm⟩
      | cons next rest => simp [MInst.setTargets,targets] at retarget

/-- Actual indexed filtering/splitting/RPO preserves a live original jump as a
jump at its real label counterpart, with the original instruction count and
parameters. The output CFG/counterpart/retargeted instruction are derived
from successful prepareAt and its proved relation, not supplied certificates. -/
theorem prepareAt_jump_counterpart {vc : VCode} {edges : Array EdgeRow} {p : EdgeVCode}
    (run : prepareAt vc edges = .ok p) (nonempty : 0 < vc.blocks.size) (labels : Prep.Lbls vc.blocks)
    {ss0 ps0 : Array (Array Nat)} (cfg0 : vc.cfg = .ok (ss0,ps0))
    {b : Nat} {vb : VBlock} {old : Label} (sourceBlock : vc.blocks[b]? = some vb)
    (live : Prep.mk (reachable ss0) b) (back : vb.insts.back? = some (.jump old)) :
    ∃ (ss3 ps3 : Array (Array Nat)) (q : Nat) (vb' : VBlock) (label : Label),
      p.code.cfg = .ok (ss3,ps3) ∧ sigmaOf vc p.code b = some q ∧ p.code.blocks[q]? = some vb' ∧
      vb'.insts.back? = some (.jump label) ∧ vb'.insts.size = vb.insts.size ∧ vb'.params = vb.params := by
  obtain ⟨_,ss3,ps3,cfg3⟩ := prepareAt_cfg run nonempty labels
  obtain ⟨q,sigma,checked⟩ := live_okAt run nonempty labels cfg0 cfg3
    (Array.getElem?_eq_some_iff.mp sourceBlock).1 live
  obtain ⟨oldBlock,vb',atOld,atNew,params,arguments,size,instructions,rest⟩ := (keptOkAt_sound checked).blocks
  rw [sourceBlock] at atOld
  cases atOld
  have index : vb.insts[vb.insts.size-1]? = some (.jump old) := by simpa only [Array.back?_eq_getElem?] using back
  obtain ⟨i,atInst,same⟩ := instructions (vb.insts.size-1) (.jump old) index
  obtain ⟨label,rfl⟩ := sameInst_jump same
  refine ⟨ss3,ps3,q,vb',label,cfg3,sigma,atNew,?_,size,params⟩
  rw [Array.back?_eq_getElem?,size]
  exact atInst

end Backend.Proof.PerEdgePrep
