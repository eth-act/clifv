import FV.Backend.Proof.LowerSeq
import FV.Backend.Proof.PerEdgeVCodeSem

/-! Straight-line segments retain the selected per-successor semantics. The
legacy single-vector variants remain unchanged. -/
namespace Backend.Proof.Driver
open Backend Backend.Proof
variable {V W : Type} {vc : VCode} {sem : ISem V W}
    {edges : Array (Array (Array Reg))}

/-- A straight-line run of a segment that falls through is a sequence of `VStep`s, if the
block continues after the segment. -/
theorem seqRun_fall_starAt {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    ∀ {ms : List MInst} {k0 : Nat} {ρ : Nat → V} {w : W} {ρ' : Nat → V} {w' : W},
    SegAt vb k0 ms → k0 + ms.length < vb.insts.size →
    seqRun sem ms ρ w = some (.fall ρ' w') →
    Star (VStepAt vc edges sem) (.run ⟨b, k0, ρ, w⟩) (.run ⟨b, k0 + ms.length, ρ', w'⟩) := by
  intro ms
  induction ms with
  | nil =>
    intro k0 ρ w ρ' w' _ _ h
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact .refl _
  | cons i ms ih =>
    intro k0 ρ w ρ' w' hseg hlt h
    obtain ⟨ops, outs, w₁, hops, hsem, hlen, hrest⟩ := seqRun_cons_fall h
    have hstep : VStepAt vc edges sem (.run ⟨b, k0, ρ, w⟩) (.run ⟨b, k0 + 1, vdefUpd ops outs ρ, w₁⟩) :=
      VStepAt.step hvb hseg.head hops hsem hlen (VNextAt.next (by simp at hlt; omega))
    have := ih hseg.tail (by simp at hlt ⊢; omega) hrest
    simp only [List.length_cons] at this ⊢
    rw [show k0 + (ms.length + 1) = k0 + 1 + ms.length by omega]
    exact .step hstep this

/-- A straight-line run of a segment that stops at instruction `k`: the `VStep`s up to it, and
the facts `VStep` needs to execute it. -/
theorem seqRun_stop_starAt {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    ∀ {ms : List MInst} {k0 : Nat} {ρ : Nat → V} {w : W} {k : Nat} {i : MInst}
      {ops : Array Operand} {ρ₁ : Nat → V} {w₁ : W} {outs : List V} {w₂ : W} {ctl : Ctl},
    SegAt vb k0 ms → seqRun sem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl) →
    Star (VStepAt vc edges sem) (.run ⟨b, k0, ρ, w⟩) (.run ⟨b, k0 + k, ρ₁, w₁⟩) ∧ k < ms.length ∧
      vb.insts[k0 + k]? = some i ∧ i.operands = .ok ops ∧
      sem i (vuses ops ρ₁) w₁ = some (outs, w₂, ctl) ∧
      outs.length = (ops.toList.filter Operand.isDef).length ∧ ctl ≠ .next := by
  intro ms
  induction ms with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ _ h; simp [seqRun] at h
  | cons i₀ ms ih =>
    intro k0 ρ w k i ops ρ₁ w₁ outs w₂ ctl hseg h
    rcases seqRun_cons_stop h with
      ⟨rfl, rfl, hops, rfl, rfl, hsem, hlen, hne⟩ | ⟨k', ops₀, outs₀, w₃, rfl, hops₀, hsem₀, hlen₀, hrest⟩
    · exact ⟨by simpa using Star.refl _, by simp, by simpa using hseg.head, hops, hsem, hlen, hne⟩
    · obtain ⟨hstar, hk, hi, hops, hsem, hlen, hne⟩ := ih hseg.tail hrest
      have hlt : k0 + 1 < vb.insts.size := by
        have := (Array.getElem?_eq_some_iff.mp hi).1; omega
      have hstep : VStepAt vc edges sem (.run ⟨b, k0, ρ, w⟩)
          (.run ⟨b, k0 + 1, vdefUpd ops₀ outs₀ ρ, w₃⟩) :=
        VStepAt.step hvb hseg.head hops₀ hsem₀ hlen₀ (VNextAt.next hlt)
      refine ⟨?_, by simp; omega, by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hi, hops,
        hsem, hlen, hne⟩
      rw [show k0 + (k' + 1) = k0 + 1 + k' by omega]
      exact .step hstep hstar

/-- Execute a complete segment through its actual branch and selected copy.
The instruction may be a jump, conditional or table branch. -/
theorem seqRun_goto_starAt {b k0 offset index target : Nat} {vb : VBlock}
    {ms : List MInst} {i : MInst} {ops : Array Operand}
    {ρ ρ₁ ρ' : Nat → V} {w w₁ w₂ : W} {outs : List V}
    (block : vc.blocks[b]? = some vb) (segment : SegAt vb k0 ms)
    (execution : seqRun sem ms ρ w = some (.stop offset i ops ρ₁ w₁ outs w₂ (.goto index)))
    (last : k0+offset+1 = vb.insts.size) (successor : succOf vc b index = some target)
    (copied : edgeEnvAt vc edges b target index (vdefUpd ops outs ρ₁) = some ρ') :
    Star (VStepAt vc edges sem) (.run ⟨b,k0,ρ,w⟩) (.run ⟨target,0,ρ',w₂⟩) := by
  obtain ⟨steps,_,instruction,operands,ran,length,_⟩ := seqRun_stop_starAt block segment execution
  exact steps.trans (.step (VStepAt.step block instruction operands ran length
    (VNextAt.goto last successor copied)) (.refl _))

end Backend.Proof.Driver
