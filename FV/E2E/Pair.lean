import FV.E2E.Guarded

/-! # Runs on pairs of worlds (agent/link-widen, stage 2)

The world-generic driver (`sim_run` over `ISem CV W`) run at `W = Arm.ArmState × Arm.ArmState`
with the paired semantics `pairSem sem` (the same instruction on both worlds, the same outputs
and control) gives two VCode runs with one outcome. This file has the generic part:

* `pairSem`, its projections (`vstep_pair`, `star_pair`, `vRetFrom_pair`, `vTrapFrom_pair`);
* `seqRun_pair`: two straight-line runs of a sub-semantics of `sem` (e.g. the guarded `csemG`)
  whose instructions go in lockstep under an invariant `R` of the two worlds are one run of
  `pairSem sem`. -/

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver

/-- Two worlds. -/
abbrev W2 := Arm.ArmState × Arm.ArmState

open Classical in
/-- **The paired semantics**: an instruction on both worlds, defined when both runs are and
give the same outputs and control. -/
noncomputable def pairSem (sem : Sem) : ISem CV W2 := fun i us p =>
  match sem i us p.1, sem i us p.2 with
  | some r1, some r2 =>
    if r1.1 = r2.1 ∧ r1.2.2 = r2.2.2 then some (r1.1, (r1.2.1, r2.2.1), r1.2.2) else none
  | _, _ => none

section
variable {sem : Sem}

theorem pairSem_eq {i : MInst} {us : List CV} {p : W2} {o : List CV} {w1 w2 : Arm.ArmState}
    {c : Ctl} (h1 : sem i us p.1 = some (o, w1, c)) (h2 : sem i us p.2 = some (o, w2, c)) :
    pairSem sem i us p = some (o, (w1, w2), c) := by
  simp [pairSem, h1, h2]

theorem pairSem_inv {i : MInst} {us : List CV} {p : W2} {o : List CV} {q : W2} {c : Ctl}
    (h : pairSem sem i us p = some (o, q, c)) :
    sem i us p.1 = some (o, q.1, c) ∧ sem i us p.2 = some (o, q.2, c) := by
  unfold pairSem at h
  split at h
  · rename_i r1 r2 h1 h2
    split at h
    · rename_i he
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      obtain ⟨o1, w1, c1⟩ := r1
      obtain ⟨o2, w2, c2⟩ := r2
      simp only at he ⊢
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨h1, h2⟩
    · cases h
  · cases h

/-- A configuration with its world mapped. -/
def _root_.Backend.Proof.VConf.mapW {V W W' : Type} (f : W → W') : VConf V W → VConf V W'
  | .run s => .run ⟨s.b, s.k, s.ρ, f s.w⟩
  | .ret vals w => .ret vals (f w)
  | .halt w => .halt (f w)

theorem vnext_map {V W W' : Type} (vc : VCode) (f : W → W') {b k n : Nat} {i : MInst}
    {uses : List V} {ρ : Nat → V} {w : W} {c : Ctl} {c' : VConf V W}
    (h : VNext vc b k n i uses ρ w c c') : VNext vc b k n i uses ρ (f w) c (c'.mapW f) := by
  cases h with
  | next hk => exact .next hk
  | goto h1 h2 h3 => exact .goto h1 h2 h3
  | ret hi => exact .ret hi
  | halt => exact .halt

theorem vstep_pair {vc : VCode} (π : W2 → Arm.ArmState) (hπ : π = Prod.fst ∨ π = Prod.snd)
    {c c' : VConf CV W2} (h : VStep vc (pairSem sem) c c') :
    VStep vc sem (c.mapW π) (c'.mapW π) := by
  cases h with
  | step hvb hi hops hsem hlen hn =>
    obtain ⟨h1, h2⟩ := pairSem_inv hsem
    refine VStep.step hvb hi hops ?_ hlen (vnext_map vc π hn)
    rcases hπ with rfl | rfl
    · exact h1
    · exact h2

theorem star_pair {vc : VCode} (π : W2 → Arm.ArmState) (hπ : π = Prod.fst ∨ π = Prod.snd)
    {c c' : VConf CV W2} (h : Star (VStep vc (pairSem sem)) c c') :
    Star (VStep vc sem) (c.mapW π) (c'.mapW π) := by
  induction h with
  | refl => exact .refl _
  | step h1 _ ih => exact .step (vstep_pair π hπ h1) ih

/-- A paired return projects to a return of each world, through the same `rets` with the same
values. -/
theorem vRetFrom_pair {vc : VCode} {vs : VState CV W2} {us : List (Reg × Reg)} {vals : List CV}
    {w : W2} (h : VRetFrom vc (pairSem sem) vs us vals w) :
    VRetFrom vc sem ⟨vs.b, vs.k, vs.ρ, vs.w.1⟩ us vals w.1 ∧
      VRetFrom vc sem ⟨vs.b, vs.k, vs.ρ, vs.w.2⟩ us vals w.2 := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hv, hsem⟩ := h
  obtain ⟨h1, h2⟩ := pairSem_inv hsem
  exact ⟨⟨b, k, ρ, w₁.1, vb, ops, outs, star_pair Prod.fst (.inl rfl) hs, hvb, hk, hops, hv, h1⟩,
    ⟨b, k, ρ, w₁.2, vb, ops, outs, star_pair Prod.snd (.inr rfl) hs, hvb, hk, hops, hv, h2⟩⟩

theorem vTrapFrom_pair {vc : VCode} {vs : VState CV W2} {c : Clif.TrapCode}
    (h : VTrapFrom vc (pairSem sem) vs c) :
    VTrapFrom vc sem ⟨vs.b, vs.k, vs.ρ, vs.w.1⟩ c ∧ VTrapFrom vc sem ⟨vs.b, vs.k, vs.ρ, vs.w.2⟩ c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc⟩ := h
  obtain ⟨h1, h2⟩ := pairSem_inv hsem
  exact ⟨⟨b, k, ρ, w.1, vb, i, ops, outs, w'.1, star_pair Prod.fst (.inl rfl) hs, hvb, hi, hops,
    h1, htc⟩, ⟨b, k, ρ, w.2, vb, i, ops, outs, w'.2, star_pair Prod.snd (.inr rfl) hs, hvb, hi, hops,
    h2, htc⟩⟩

/-- A straight-line end with its worlds mapped. -/
def _root_.Backend.Proof.SeqEnd.mapW {V W W' : Type} (f : W → W') : SeqEnd V W → SeqEnd V W'
  | .fall ρ w => .fall ρ (f w)
  | .stop k i ops ρ w outs w' ctl => .stop k i ops ρ (f w) outs (f w') ctl

theorem _root_.Backend.Proof.SeqEnd.mapW_succ {V W W' : Type} (f : W → W') (e : SeqEnd V W) :
    (e.succ).mapW f = (e.mapW f).succ := by
  cases e <;> rfl

/-- The invariant `R` holds of the worlds of a paired end. -/
def _root_.Backend.Proof.SeqEnd.Rel (R : Arm.ArmState → Arm.ArmState → Prop) : SeqEnd CV W2 → Prop
  | .fall _ w => R w.1 w.2
  | .stop _ _ _ _ w _ w' _ => R w.1 w.2 ∧ R w'.1 w'.2

theorem _root_.Backend.Proof.SeqEnd.rel_succ {R : Arm.ArmState → Arm.ArmState → Prop} {e : SeqEnd CV W2}
    (h : e.Rel R) : e.succ.Rel R := by
  cases e <;> exact h

/-- **Two straight-line runs in lockstep are one paired run**: the runs of a semantics `semA`
contained in `sem` (`hsub`) on two worlds related by `R`, whose instructions keep `R` and give
the same outputs and control (`hstep`, for the instructions of the run). -/
theorem seqRun_pair {semA : Sem}
    (hsub : ∀ i us w r, semA i us w = some r → sem i us w = some r)
    {R : Arm.ArmState → Arm.ArmState → Prop} :
    ∀ (ms : List MInst),
    (∀ i ∈ ms, ∀ us w w' o w₁ c o' w₁' c', R w w' → semA i us w = some (o, w₁, c) →
      semA i us w' = some (o', w₁', c') → o = o' ∧ c = c' ∧ R w₁ w₁') →
    ∀ (ρ : Nat → CV) (w w' : Arm.ArmState) (e e' : SeqEnd CV Arm.ArmState), R w w' →
      seqRun semA ms ρ w = some e → seqRun semA ms ρ w' = some e' →
      ∃ ep, seqRun (pairSem sem) ms ρ (w, w') = some ep ∧ ep.mapW Prod.fst = e ∧
        ep.mapW Prod.snd = e' ∧ ep.Rel R
  | [], _, ρ, w, w', e, e', hR, h, h' => by
    simp only [seqRun, Option.some.injEq] at h h'
    subst h h'
    exact ⟨.fall ρ (w, w'), rfl, rfl, rfl, hR⟩
  | i :: ms, hstep, ρ, w, w', e, e', hR, h, h' => by
    simp only [seqRun] at h h' ⊢
    cases hops : i.operands with
    | error => simp [hops] at h
    | ok ops =>
      simp only [hops] at h h' ⊢
      cases hs : semA i (vuses ops ρ) w with
      | none => simp [hs] at h
      | some r =>
        obtain ⟨o, w₁, c⟩ := r
        cases hs' : semA i (vuses ops ρ) w' with
        | none => simp [hs'] at h'
        | some r' =>
          obtain ⟨o', w₁', c'⟩ := r'
          simp only [hs] at h
          simp only [hs'] at h'
          obtain ⟨rfl, rfl, hR1⟩ := hstep i List.mem_cons_self _ w w' o w₁ c o' w₁' c' hR hs hs'
          rw [pairSem_eq (hsub _ _ _ _ hs) (hsub _ _ _ _ hs')]
          simp only
          by_cases hlen : o.length = (ops.toList.filter Operand.isDef).length
          · rw [if_pos hlen] at h h' ⊢
            cases c with
            | next =>
              simp only [Option.map_eq_some_iff] at h h' ⊢
              obtain ⟨e1, h1, rfl⟩ := h
              obtain ⟨e2, h2, rfl⟩ := h'
              obtain ⟨ep, hp, hp1, hp2, hpr⟩ := seqRun_pair hsub ms
                (fun j hj => hstep j (List.mem_cons_of_mem _ hj)) _ w₁ w₁' e1 e2 hR1 h1 h2
              exact ⟨ep.succ, ⟨ep, hp, rfl⟩, by rw [SeqEnd.mapW_succ, hp1],
                by rw [SeqEnd.mapW_succ, hp2], SeqEnd.rel_succ hpr⟩
            | _ =>
              simp only [Option.some.injEq] at h h' ⊢
              subst h h'
              exact ⟨_, rfl, rfl, rfl, hR, hR1⟩
          · rw [if_neg hlen] at h
            cases h

end

end E2E
