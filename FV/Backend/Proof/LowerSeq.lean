import FV.Backend.Proof.IselContract

/-!
# Straight-line VCode execution (M7 driver, M4 rule statements)

`seqRun sem ms ρ w` (`Backend.Proof.seqRun`, `IselContract.lean`) runs the instruction list `ms` with `VStep`'s per-instruction rule (read the
use vregs, write early then late defs) until the list ends (`fall`) or an instruction's control
is not `next` (`stop`, with the state *before* that instruction and its outputs). A segment of a
VCode block that `seqRun` executes is a sequence of `VStep`s (`seqRun_fall_star`,
`seqRun_stop_star`). Parametric in the values `V` and the world `W`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof

section
variable {V W : Type}

/-- The segment `ms` is at index `k0` of block `vb`. -/
def SegAt (vb : VBlock) (k0 : Nat) (ms : List MInst) : Prop :=
  ∀ k (h : k < ms.length), vb.insts[k0 + k]? = some ms[k]

theorem SegAt.tail {vb : VBlock} {k0 : Nat} {i : MInst} {ms : List MInst}
    (h : SegAt vb k0 (i :: ms)) : SegAt vb (k0 + 1) ms := by
  intro k hk
  have := h (k + 1) (by simp; omega)
  simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

theorem SegAt.head {vb : VBlock} {k0 : Nat} {i : MInst} {ms : List MInst}
    (h : SegAt vb k0 (i :: ms)) : vb.insts[k0]? = some i := by
  have := h 0 (by simp)
  simp only [List.getElem_cons_zero, Nat.add_zero] at this
  exact this

theorem SegAt.append_left {vb : VBlock} {k0 : Nat} {ms ns : List MInst}
    (h : SegAt vb k0 (ms ++ ns)) : SegAt vb k0 ms := by
  intro k hk
  have := h k (by simp; omega)
  rwa [List.getElem_append_left hk] at this

theorem SegAt.append_right {vb : VBlock} {k0 : Nat} {ms ns : List MInst}
    (h : SegAt vb k0 (ms ++ ns)) : SegAt vb (k0 + ms.length) ns := by
  intro k hk
  have := h (ms.length + k) (by simp; omega)
  rw [List.getElem_append_right (by omega)] at this
  simpa [Nat.add_assoc] using this

theorem SegAt.lt {vb : VBlock} {k0 : Nat} {ms : List MInst} (h : SegAt vb k0 ms) {k : Nat}
    (hk : k < ms.length) : k0 + k < vb.insts.size :=
  (Array.getElem?_eq_some_iff.mp (h k hk)).1

theorem seqRun_cons_fall {sem : ISem V W} {i : MInst} {ms : List MInst} {ρ : Nat → V} {w : W}
    {ρ' : Nat → V} {w' : W} (h : seqRun sem (i :: ms) ρ w = some (.fall ρ' w')) :
    ∃ ops outs w₁, i.operands = .ok ops ∧ sem i (vuses ops ρ) w = some (outs, w₁, .next) ∧
      outs.length = (ops.toList.filter Operand.isDef).length ∧
      seqRun sem ms (vdefUpd ops outs ρ) w₁ = some (.fall ρ' w') := by
  unfold seqRun at h
  split at h
  · cases h
  · rename_i ops hops
    split at h
    · cases h
    · rename_i outs w₁ ctl hsem
      split at h
      · rename_i hlen
        split at h
        · refine ⟨ops, outs, w₁, hops, hsem, hlen, ?_⟩
          cases hr : seqRun sem ms (vdefUpd ops outs ρ) w₁ with
          | none => rw [hr] at h; cases h
          | some e =>
            rw [hr] at h
            cases e <;> simp [SeqEnd.succ] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
        · cases h
      · cases h

theorem seqRun_cons_stop {sem : ISem V W} {i : MInst} {ms : List MInst} {ρ : Nat → V} {w : W}
    {k : Nat} {i' : MInst} {ops' : Array Operand} {ρ₁ : Nat → V} {w₁ : W} {outs' : List V}
    {w₂ : W} {ctl' : Ctl}
    (h : seqRun sem (i :: ms) ρ w = some (.stop k i' ops' ρ₁ w₁ outs' w₂ ctl')) :
    (k = 0 ∧ i' = i ∧ i.operands = .ok ops' ∧ ρ₁ = ρ ∧ w₁ = w ∧
      sem i (vuses ops' ρ) w = some (outs', w₂, ctl') ∧
      outs'.length = (ops'.toList.filter Operand.isDef).length ∧ ctl' ≠ .next) ∨
    (∃ k' ops outs w₃, k = k' + 1 ∧ i.operands = .ok ops ∧
      sem i (vuses ops ρ) w = some (outs, w₃, .next) ∧
      outs.length = (ops.toList.filter Operand.isDef).length ∧
      seqRun sem ms (vdefUpd ops outs ρ) w₃ = some (.stop k' i' ops' ρ₁ w₁ outs' w₂ ctl')) := by
  unfold seqRun at h
  split at h
  · cases h
  · rename_i ops hops
    split at h
    · cases h
    · rename_i outs w₃ ctl hsem
      split at h
      · rename_i hlen
        split at h
        · right
          cases hr : seqRun sem ms (vdefUpd ops outs ρ) w₃ with
          | none => rw [hr] at h; cases h
          | some e =>
            rw [hr] at h
            cases e with
            | fall => simp [SeqEnd.succ] at h
            | stop k'' =>
              simp only [Option.map_some, SeqEnd.succ, Option.some.injEq, SeqEnd.stop.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
              exact ⟨k'', ops, outs, w₃, rfl, hops, hsem, hlen, hr⟩
        · rename_i hne
          left
          simp only [Option.some.injEq, SeqEnd.stop.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
          exact ⟨rfl, rfl, hops, rfl, rfl, hsem, hlen, fun e => hne e⟩
      · cases h

variable {vc : VCode} {sem : ISem V W}

/-- A straight-line run of a segment that falls through is a sequence of `VStep`s, if the
block continues after the segment. -/
theorem seqRun_fall_star {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    ∀ {ms : List MInst} {k0 : Nat} {ρ : Nat → V} {w : W} {ρ' : Nat → V} {w' : W},
    SegAt vb k0 ms → k0 + ms.length < vb.insts.size →
    seqRun sem ms ρ w = some (.fall ρ' w') →
    Star (VStep vc sem) (.run ⟨b, k0, ρ, w⟩) (.run ⟨b, k0 + ms.length, ρ', w'⟩) := by
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
    have hstep : VStep vc sem (.run ⟨b, k0, ρ, w⟩) (.run ⟨b, k0 + 1, vdefUpd ops outs ρ, w₁⟩) :=
      VStep.step hvb hseg.head hops hsem hlen (VNext.next (by simp at hlt; omega))
    have := ih hseg.tail (by simp at hlt ⊢; omega) hrest
    simp only [List.length_cons] at this ⊢
    rw [show k0 + (ms.length + 1) = k0 + 1 + ms.length by omega]
    exact .step hstep this

/-- A straight-line run of a segment that stops at instruction `k`: the `VStep`s up to it, and
the facts `VStep` needs to execute it. -/
theorem seqRun_stop_star {b : Nat} {vb : VBlock} (hvb : vc.blocks[b]? = some vb) :
    ∀ {ms : List MInst} {k0 : Nat} {ρ : Nat → V} {w : W} {k : Nat} {i : MInst}
      {ops : Array Operand} {ρ₁ : Nat → V} {w₁ : W} {outs : List V} {w₂ : W} {ctl : Ctl},
    SegAt vb k0 ms → seqRun sem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl) →
    Star (VStep vc sem) (.run ⟨b, k0, ρ, w⟩) (.run ⟨b, k0 + k, ρ₁, w₁⟩) ∧ k < ms.length ∧
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
      have hstep : VStep vc sem (.run ⟨b, k0, ρ, w⟩)
          (.run ⟨b, k0 + 1, vdefUpd ops₀ outs₀ ρ, w₃⟩) :=
        VStep.step hvb hseg.head hops₀ hsem₀ hlen₀ (VNext.next hlt)
      refine ⟨?_, by simp; omega, by simpa [Nat.add_assoc, Nat.add_comm 1 k'] using hi, hops,
        hsem, hlen, hne⟩
      rw [show k0 + (k' + 1) = k0 + 1 + k' by omega]
      exact .step hstep hstar

/-! ## Frame: a run changes only def vregs -/

theorem writeV_other {ρ : Nat → V} {n : Nat} :
    ∀ {dv : List (Operand × V)}, (∀ p ∈ dv, p.1.vreg ≠ n) → writeV ρ dv n = ρ n := by
  intro dv
  induction dv generalizing ρ with
  | nil => intro _; rfl
  | cons p dv ih =>
    intro h
    simp only [writeV, List.foldl_cons] at ih ⊢
    rw [ih (fun q hq => h q (List.mem_cons_of_mem _ hq))]
    have hp := Ne.symm (h p (by simp))
    simp [upd, hp]

theorem vdefUpd_other {ops : Array Operand} {outs : List V} {ρ : Nat → V} {n : Nat}
    (h : n ∉ (ops.toList.filter Operand.isDef).map (·.vreg)) : vdefUpd ops outs ρ n = ρ n := by
  have hne : ∀ p ∈ (ops.toList.filter Operand.isDef).zip outs, p.1.vreg ≠ n := by
    intro p hp e
    exact h (List.mem_map.mpr ⟨p.1, List.of_mem_zip hp |>.1, e⟩)
  unfold vdefUpd
  rw [writeV_other (fun p hp => hne p (List.mem_filter.mp hp).1),
    writeV_other (fun p hp => hne p (List.mem_filter.mp hp).1)]

theorem seqRun_fall_frame {n : Nat} :
    ∀ {ms : List MInst} {ρ : Nat → V} {w : W} {ρ' : Nat → V} {w' : W},
    (∀ m ∈ ms, n ∉ vdefs m) → seqRun sem ms ρ w = some (.fall ρ' w') → ρ' n = ρ n := by
  intro ms
  induction ms with
  | nil =>
    intro ρ w ρ' w' _ h
    simp only [seqRun, Option.some.injEq, SeqEnd.fall.injEq] at h
    rw [h.1]
  | cons i ms ih =>
    intro ρ w ρ' w' hn h
    obtain ⟨ops, outs, w₁, hops, _, _, hrest⟩ := seqRun_cons_fall h
    rw [ih (fun m hm => hn m (List.mem_cons_of_mem _ hm)) hrest]
    have := hn i (by simp)
    simp only [vdefs, hops] at this
    exact vdefUpd_other this

theorem seqRun_stop_frame {n : Nat} :
    ∀ {ms : List MInst} {ρ : Nat → V} {w : W} {k : Nat} {i : MInst} {ops : Array Operand}
      {ρ₁ : Nat → V} {w₁ : W} {outs : List V} {w₂ : W} {ctl : Ctl},
    (∀ m ∈ ms, n ∉ vdefs m) → seqRun sem ms ρ w = some (.stop k i ops ρ₁ w₁ outs w₂ ctl) →
    ρ₁ n = ρ n ∧ vdefUpd ops outs ρ₁ n = ρ n := by
  intro ms
  induction ms with
  | nil => intro _ _ _ _ _ _ _ _ _ _ _ h; simp [seqRun] at h
  | cons i₀ ms ih =>
    intro ρ w k i ops ρ₁ w₁ outs w₂ ctl hn h
    rcases seqRun_cons_stop h with
      ⟨rfl, rfl, hops, rfl, rfl, _, _, _⟩ | ⟨k', ops₀, outs₀, w₃, rfl, hops₀, _, _, hrest⟩
    · have := hn i (by simp)
      simp only [vdefs, hops] at this
      exact ⟨rfl, vdefUpd_other this⟩
    · have h1 := ih (fun m hm => hn m (List.mem_cons_of_mem _ hm)) hrest
      have := hn i₀ (by simp)
      simp only [vdefs, hops₀] at this
      rw [h1.1, h1.2, vdefUpd_other this]
      exact ⟨rfl, rfl⟩

end

end Backend.Proof.Driver
