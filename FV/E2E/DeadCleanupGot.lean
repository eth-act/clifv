import FV.E2E.GotFlow
import FV.E2E.DeadCleanupRealizes

namespace E2E
open Backend Backend.Proof Backend.DeadCleanup
variable {vc : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {X : ExtSem}

theorem gotInv_step_value {s : VState CV Arm.ArmState} {c' : VConf CV Arm.ArmState}
    (hI : GotInv vc X s) (h : VStep vc (valueSem F ctx X) (.run s) c') :
    VStep vc (valueSemV (GotV vc) F ctx X) (.run s) c' ∧ ∀ s', c' = .run s' → GotInv vc X s' := by
  cases h with
  | @step b k ρ w vb i ops outs w' ctl _ hvb hi hops hsem hlen hnext =>
  refine ⟨VStep.step hvb hi hops ?_ hlen hnext, ?_⟩
  · simp only [valueSemV]
    by_cases hp : Backend.DeadCleanup.pureForm i = true
    · simpa [Backend.DeadCleanup.valueSem, hp, vuses] using hsem
    simp only [hp, Bool.false_eq_true, ite_false]
    have hsem0 : csem F ctx X i (vuses ops ρ) w = some (outs, w', ctl) := by
      simpa [Backend.DeadCleanup.valueSem, hp, vuses] using hsem
    rw [csemV_eq]
    · exact hsem0
    · intro info hinfo t n ops' hd hgv hops' hhead
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
        simp [hhead, hv', lo64_ofX_got]
  · intro s' hc
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
        simp only [Backend.DeadCleanup.valueSem, Backend.DeadCleanup.pureForm, ite_false, csem, Option.some.injEq, Prod.mk.injEq] at hsem
        obtain ⟨rfl, rfl, -⟩ := hsem
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

/-- **Runs**: a run of `csem` from a state with the invariant is a run of `valueSemV (GotV vc)`,
ending in a state with the invariant. -/
theorem gotInv_star_value {s s' : VState CV Arm.ArmState} (hI : GotInv vc X s)
    (h : Star (VStep vc (valueSem F ctx X)) (.run s) (.run s')) :
    Star (VStep vc (valueSemV (GotV vc) F ctx X)) (.run s) (.run s') ∧ GotInv vc X s' := by
  generalize ha : (VConf.run s : VConf CV Arm.ArmState) = a at h
  generalize hb : (VConf.run s' : VConf CV Arm.ArmState) = b at h
  induction h generalizing s with
  | refl => subst ha; cases hb; exact ⟨.refl _, hI⟩
  | @step a1 a2 a3 h1 h2 ih =>
    subst ha
    cases a2 with
    | run s2 =>
      obtain ⟨h1', hI2⟩ := gotInv_step_value hI h1
      obtain ⟨h2', hI'⟩ := ih (hI2 s2 rfl) rfl hb
      exact ⟨.step h1' h2', hI'⟩
    | ret vals w => subst hb; cases h2 with | step h _ => cases h
    | halt w => subst hb; cases h2 with | step h _ => cases h

/-- **A returning VCode run of `csem` is one of `valueSemV (GotV vc)`.** -/
theorem vReturns_gotV_value {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {us : List (Reg × Reg)}
    {vals : List CV} {w : Arm.ArmState} (h : VReturns vc (valueSem F ctx X) ρ₀ w₀ us vals w) :
    VReturns vc (valueSemV (GotV vc) F ctx X) ρ₀ w₀ us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  obtain ⟨hs', -⟩ := gotInv_star_value (gotInv_entry vc X ρ₀ w₀) hs
  exact ⟨b, k, ρ, w₁, vb, ops, outs, hs', hvb, hk, hops, hvals, by
    simp only [valueSemV, Backend.DeadCleanup.pureForm, ite_false]
    rw [csemV_eq fun info h => by rcases h with h | ⟨_, h⟩ <;> cases h]; exact hsem⟩

/-- **A trapping VCode run of `csem` is one of `valueSemV (GotV vc)`.** -/
theorem vTraps_gotV_value {ρ₀ : Nat → CV} {w₀ : Arm.ArmState} {c : Clif.TrapCode}
    (h : VTraps vc (valueSem F ctx X) ρ₀ w₀ c) : VTraps vc (valueSemV (GotV vc) F ctx X) ρ₀ w₀ c := by
  obtain ⟨b, k, ρ, w, vb, i, ops, outs, w', hs, hvb, hi, hops, hsem, htc⟩ := h
  obtain ⟨hs', -⟩ := gotInv_star_value (gotInv_entry vc X ρ₀ w₀) hs
  refine ⟨b, k, ρ, w, vb, i, ops, outs, w', hs', hvb, hi, hops, ?_, htc⟩
  have hp : Backend.DeadCleanup.pureForm i = false := by
    cases he : Backend.DeadCleanup.pureForm i
    · rfl
    · have hn := (Backend.DeadCleanup.valueSem_pure he hsem).2
      cases hn
  have hsem0 : csem F ctx X i (vuses ops ρ) w = some (outs, w', .halt) := by
    simpa [Backend.DeadCleanup.valueSem, hp, vuses] using hsem
  obtain ⟨-, hform⟩ := csem_halt hsem0
  simp only [valueSemV, hp, Bool.false_eq_true, ite_false]
  rw [csemV_eq fun info h => by
    rcases h with rfl | ⟨_, rfl⟩ <;> rcases hform with ⟨_, e⟩ | ⟨_, _, e, _⟩ <;> cases e]
  exact hsem0

end E2E
