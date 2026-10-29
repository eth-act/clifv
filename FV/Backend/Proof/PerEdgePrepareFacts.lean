module

public import FV.Backend.RegallocPerEdgePrepare
public import FV.Backend.Proof.RegallocLemmas

@[expose] public section

namespace Backend.Proof.PerEdgePrep
open Backend Backend.Proof
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
/-- Actual successful prepareAt keeps all non-block code metadata, independently
of its filtering/splitting/RPO decisions. -/
theorem prepareAt_fields {vc : VCode} {edges : Array (Array (Array Reg))} {p : EdgeVCode}
    (h : prepareAt vc edges = .ok p) : p.code.name = vc.name ∧ p.code.classes = vc.classes ∧
    p.code.slotBytes = vc.slotBytes ∧ p.code.outgoing = vc.outgoing ∧ p.code.rulesFired = vc.rulesFired := by
  unfold prepareAt at h
  obtain ⟨⟨ss0,ps0⟩,cfg0,h⟩ := Except.bind_ok h
  dsimp only at h
  cases count : (edges.size != vc.blocks.size) with
  | true => simp [count,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
  | false =>
    simp only [count,Bool.false_eq_true,ite_false] at h
    obtain ⟨answer,rows,h⟩ := Except.bind_ok h
    cases answer
    obtain ⟨⟨ss1,ps1⟩,cfg1,h⟩ := Except.bind_ok h
    dsimp only at h
    cases incoming : (!(ps1[0]?.getD #[]).isEmpty) with
    | true => simp [incoming,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
    | false =>
      simp only [incoming,Bool.false_eq_true,ite_false] at h
      split at h
      · simp [bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
      · obtain ⟨state,loop,h⟩ := Except.bind_ok h
        obtain ⟨⟨ss2,ps2⟩,cfg2,h⟩ := Except.bind_ok h
        cases h
        exact ⟨rfl,rfl,rfl,rfl,rfl⟩
end Backend.Proof.PerEdgePrep
