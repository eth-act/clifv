import FV.E2E.GotFlow
import FV.E2E.UnwindValueSem
import FV.E2E.UnwindStatement

/-!
# Calls through the GOT with unwinding (S10f, #233)

`FV/E2E/GotFlow.lean`/`FV/E2E/DeadCleanupGot.lean` for the semantics with unwinding: a VCode run of
`csemU` (resp. the value semantics `valueSemU`) is one of `csemVU (GotV vc)` (resp.
`valueSemVU (GotV vc)`), the calls through the GOT pinned to their symbol (M6's semantics), for
its returns, traps and exceptional ends.

* `csemVU_eq`: `csemVU gv` is `csemU` where the guard of the calls holds.
* `gotGuard_of_inv`: at a call of a run state with the invariant `GotInv` the guard holds.
* `GotPair vc X sem₁ sem₂`: what the transfer needs of the pair (they agree at the instructions of
  states with the invariant; `sem₁`'s GOT load gives the symbol's address); instances
  `gotPair_csemU`, `gotPair_valueU`.
* `gotInv_star_gen`, `vReturns_gotV_gen`, `vTraps_gotV_gen`, `vUnwinds_gotV_gen`.
-/

namespace E2E

open Backend Backend.Proof Backend.DeadCleanup

/-- `csemVU gv` is `csemU` where the guard of the calls holds (`csemV_eq`'s counterpart). -/
theorem csemVU_eq {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}
    {XR : XRaise} {i : MInst} {uses : List CV} {w : Arm.ArmState}
    (h : ∀ info, (i = .call info ∨ ∃ ti, i = .tryCall info ti) → gotGuard gv X info uses) :
    csemVU gv F ctx X XR i uses w = csemU F ctx X XR i uses w := by
  unfold csemVU
  split
  · simp only [h _ (.inl rfl), ↓reduceIte]
  · simp only [h _ (.inr ⟨_, rfl⟩), ↓reduceIte]
  · rfl

variable {vc : VCode} {X : ExtSem}

/-- **At a call of a run state with the invariant `GotInv`, the guard of the GOT pins holds.** -/
theorem gotGuard_of_inv {b k : Nat} {ρ : Nat → CV} {w : Arm.ArmState} (hI : GotInv vc X ⟨b, k, ρ, w⟩)
    {vb : VBlock} {i : MInst} {ops : Array Operand} (hvb : vc.blocks[b]? = some vb)
    (hi : vb.insts[k]? = some i) (hops : i.operands = .ok ops) :
    ∀ info, (i = .call info ∨ ∃ ti, i = .tryCall info ti) → gotGuard (GotV vc) X info (vuses ops ρ) := by
  intro info hinfo t n ops' hd hgv hops' hhead
  have hops'' : (MInst.call info).operands = .ok ops := by
    rcases hinfo with rfl | ⟨ti, rfl⟩
    · exact hops
    · rw [← operands_tryCall_call info ti]; exact hops
  rw [hops''] at hops'
  cases hops'
  obtain ⟨j, hjk, hj⟩ := hgv.2 b vb k info hvb
    (by rcases hinfo with rfl | ⟨ti, rfl⟩; exact .inl hi; exact .inr ⟨ti, hi⟩) hd
  have hv := hI t n vb j hgv hvb hjk hj
  cases hf : ops.toList.filter Operand.isUse with
  | nil => rw [hf] at hhead; cases hhead
  | cons o rest =>
    rw [hf] at hhead
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hhead
    have hv' : ρ t = ofX (X.sym n 0) := hv
    simp [vuses, hf, hhead, hv', lo64_ofX_got]

/-- **What the GOT transfer needs of a pair of semantics**: `sem₂` is `sem₁` at the instructions
of run states with the invariant, and `sem₁`'s GOT load defines the symbol's address. -/
structure GotPair (vc : VCode) (X : ExtSem) (sem₁ sem₂ : Sem) : Prop where
  agree : ∀ b k ρ w vb i ops, GotInv vc X ⟨b, k, ρ, w⟩ → vc.blocks[b]? = some vb →
    vb.insts[k]? = some i → i.operands = .ok ops →
    sem₂ i (vuses ops ρ) w = sem₁ i (vuses ops ρ) w
  got : ∀ t n uses w outs w' ctl,
    sem₁ (.loadExtNameGot (.vreg t .int) n) uses w = some (outs, w', ctl) →
    outs = [ofX (X.sym n 0)]

variable {sem₁ sem₂ : Sem}

/-- **One step**: from a state with the invariant, a `sem₁` step is a `sem₂` step and keeps the
invariant. -/
theorem gotInv_step_gen (hG : GotPair vc X sem₁ sem₂) {s : VState CV Arm.ArmState}
    {c' : VConf CV Arm.ArmState} (hI : GotInv vc X s) (h : VStep vc sem₁ (.run s) c') :
    VStep vc sem₂ (.run s) c' ∧ ∀ s', c' = .run s' → GotInv vc X s' := by
  cases h with
  | @step b k ρ w vb i ops outs w' ctl _ hvb hi hops hsem hlen hnext =>
  refine ⟨VStep.step hvb hi hops ((hG.agree b k ρ w vb i ops hI hvb hi hops).trans hsem) hlen
    hnext, ?_⟩
  intro s' hc
  cases hnext with
  | goto _ _ _ =>
    cases hc
    intro _ _ _ _ _ _ hj
    exact absurd hj (Nat.not_lt_zero _)
  | ret _ => cases hc
  | halt => cases hc
  | next hk =>
    cases hc
    intro t n vb' j hgv hvb' hj hjinst
    rw [hvb] at hvb'
    cases hvb'
    by_cases hdef : ∃ o ∈ ops.toList, o.isDef = true ∧ o.vreg = t
    · -- the step is the `loadExtNameGot t n` itself
      have e := hgv.1 b vb k i ops hvb hi hops hdef
      subst e
      have ho : ops = #[⟨t, .int, .def, .late, .reg⟩] := by
        have : (MInst.loadExtNameGot (.vreg t .int) n).operands =
            .ok #[⟨t, .int, .def, .late, .reg⟩] := rfl
        rw [this] at hops
        cases hops
        rfl
      subst ho
      obtain rfl := hG.got _ _ _ _ _ _ _ hsem
      simp [writeV, upd, Operand.isDef, Operand.isEarly, Operand.isLate]
    · have hne : ∀ (L : List (Operand × CV)), (∀ p ∈ L, p.1 ∈ ops.toList ∧ p.1.isDef = true) →
          ∀ p ∈ L, p.1.vreg ≠ t := fun L hL p hp e => hdef ⟨p.1, (hL p hp).1, (hL p hp).2, e⟩
      simp only
      rw [writeV_ne _ _ (hne _ fun p hp => mem_defs_zip (List.mem_filter.mp hp).1),
        writeV_ne _ _ (hne _ fun p hp => mem_defs_zip (List.mem_filter.mp hp).1)]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjk | rfl
      · exact hI t n vb j hgv hvb hjk hjinst
      · rw [hi] at hjinst
        cases hjinst
        exact absurd ⟨⟨t, .int, .def, .late, .reg⟩, by
          have : (MInst.loadExtNameGot (.vreg t .int) n).operands =
              .ok #[⟨t, .int, .def, .late, .reg⟩] := rfl
          rw [this] at hops
          cases hops
          simp, rfl, rfl⟩ hdef

/-- **Runs**: a run of `sem₁` from a state with the invariant is a run of `sem₂`, ending in a
state with the invariant. -/
theorem gotInv_star_gen (hG : GotPair vc X sem₁ sem₂) {s s' : VState CV Arm.ArmState}
    (hI : GotInv vc X s) (h : Star (VStep vc sem₁) (.run s) (.run s')) :
    Star (VStep vc sem₂) (.run s) (.run s') ∧ GotInv vc X s' := by
  generalize ha : (VConf.run s : VConf CV Arm.ArmState) = a at h
  generalize hb : (VConf.run s' : VConf CV Arm.ArmState) = b at h
  induction h generalizing s with
  | refl => subst ha; cases hb; exact ⟨.refl _, hI⟩
  | @step a1 a2 a3 h1 h2 ih =>
    subst ha
    cases a2 with
    | run s2 =>
      obtain ⟨h1', hI2⟩ := gotInv_step_gen hG hI h1
      obtain ⟨h2', hI'⟩ := ih (hI2 s2 rfl) rfl hb
      exact ⟨.step h1' h2', hI'⟩
    | ret vals w => subst hb; cases h2 with | step h _ => cases h
    | halt w => subst hb; cases h2 with | step h _ => cases h

theorem vReturns_gotV_gen (hG : GotPair vc X sem₁ sem₂) {ρ₀ : Nat → CV} {w₀ : Arm.ArmState}
    {us : List (Reg × Reg)} {vals : List CV} {w : Arm.ArmState}
    (h : VReturns vc sem₁ ρ₀ w₀ us vals w) : VReturns vc sem₂ ρ₀ w₀ us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  obtain ⟨hs', hI⟩ := gotInv_star_gen hG (gotInv_entry vc X ρ₀ w₀) hs
  refine ⟨b, k, ρ, w₁, vb, ops, outs, hs', hvb, hk, hops, hvals, ?_⟩
  rw [hvals, hG.agree b k ρ w₁ vb _ ops hI hvb hk hops, ← hvals]
  exact hsem

theorem vTraps_gotV_gen (hG : GotPair vc X sem₁ sem₂) {ρ₀ : Nat → CV} {w₀ : Arm.ArmState}
    {c : Clif.TrapCode} (h : VTraps vc sem₁ ρ₀ w₀ c) : VTraps vc sem₂ ρ₀ w₀ c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc⟩ := h
  obtain ⟨hs', hI⟩ := gotInv_star_gen hG (gotInv_entry vc X ρ₀ w₀) hs
  exact ⟨b, k, ρ, w, vb, i, ops, outs, w', hs', hvb, hi, hops,
    (hG.agree b k ρ w vb i ops hI hvb hi hops).trans hsem, htc⟩

theorem vUnwinds_gotV_gen (hG : GotPair vc X sem₁ sem₂) {XR : XRaise} {ρ₀ : Nat → CV}
    {w₀ : Arm.ArmState} {obj : BitVec 64} {w : Arm.ArmState}
    (h : VUnwinds vc sem₁ XR ρ₀ w₀ obj w) : VUnwinds vc sem₂ XR ρ₀ w₀ obj w := by
  obtain ⟨b, k, ρ, w₁, vb, info, ops, outs, hs, hvb, hi, hops, hraise, hsem, hlen⟩ := h
  obtain ⟨hs', hI⟩ := gotInv_star_gen hG (gotInv_entry vc X ρ₀ w₀) hs
  exact ⟨b, k, ρ, w₁, vb, info, ops, outs, hs', hvb, hi, hops, hraise,
    (hG.agree b k ρ w₁ vb _ ops hI hvb hi hops).trans hsem, hlen⟩

/-! ## The instances -/

/-- `csemU` and `csemVU (GotV vc)`. -/
theorem gotPair_csemU (F : BitVec 64 → Prop) (ctx : FnCtx) (XR : XRaise) :
    GotPair vc X (csemU F ctx X XR) (csemVU (GotV vc) F ctx X XR) where
  agree _ _ _ _ _ _ _ hI hvb hi hops := csemVU_eq (gotGuard_of_inv hI hvb hi hops)
  got _ _ _ _ _ _ _ h := by
    simp only [csemU, csem, Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm

/-- `valueSemU` and `valueSemVU (GotV vc)`. -/
theorem gotPair_valueU (F : BitVec 64 → Prop) (ctx : FnCtx) (XR : XRaise) :
    GotPair vc X (valueSemU F ctx X XR) (valueSemVU (GotV vc) F ctx X XR) where
  agree _ _ _ _ _ _ _ hI hvb hi hops := by
    simp only [valueSemVU, valueSemU]
    split
    · rfl
    · exact csemVU_eq (gotGuard_of_inv hI hvb hi hops)
  got _ _ _ _ _ _ _ h := by
    simp only [valueSemU, pureForm, Bool.false_eq_true, ite_false, csemU, csem,
      Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm

end E2E
