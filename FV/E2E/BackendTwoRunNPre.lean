import FV.E2E.BackendTwoRunL
import FV.E2E.BackendPrefixI

/-!
# The prefix two-run route: the semantics of the first `N` calls (SEM1 #537, #713)

`backend_twoRunLERWZ` takes one external semantics `XI` and `ActEntryPR` (the contracts of every
call) for both activations. At the link the second activation meets the contracts of the first
run's `XI` only up to the call where the two runs are known to be locked (#713). The prefix route
runs both activations in `XI.upTo N` (the calls `j < N` of `XI`, failing calls from `N` on), whose
contracts `ActEntryPRN … N` gives (`ActEntryPRN.upTo`), along the paired run of `XI` cut at its
counter `N`:

* `armStepX_upTo`, **`ActEntryPRN.upTo`**;
* `pairSemD_upTo_eq`, `vstar_pairDI_upTo` (the paired run to counter `≤ N` is one of
  `XI.upTo N`), `pairDI_upTo_sub` (a step of `XI.upTo N` is one of `XI`);
* `vstar_split_ctr`: a counted run from counter `≤ N` to counter `> N` passes the step from
  counter `N` to `N + 1`;
* `pstar_of_projSB`: `pstar_of_projS` with the pair guard `StepOrRet` taken in a larger
  semantics.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem armStepX_upTo (XI : ExtSemI) (N j : Nat) (H : ArmHooks) (fa : FnAsm) :
    ArmStepX ((XI.upTo N).at j) H fa = ArmStepX (XI.at j) H fa := rfl

/-- **`ActEntryPRN … N` is `ActEntryPR` of the semantics of the first `N` calls.** -/
theorem ActEntryPRN.upTo {vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    {K : Nat} {F G : BitVec 64 → Prop} {XI : ExtSemI} {H : ArmHooks} {base ra : BitVec 64}
    {Kp : Nat} {c : BitVec 64} {P : Nat → BitVec 64 → BitVec 8} {R : Nat → Arm.ArmState}
    {s w₀ : Arm.ArmState} {N : Nat}
    (h : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp c P R s w₀ N) :
    ActEntryPR vcp rf af fa fb K F G (XI.upTo N) H base ra Kp c P R s w₀ := by
  refine ⟨h.abi, h.stack, h.gfree, h.hF, h.proph, h.regp, fun n => ?_, fun ht n => ?_,
    fun ht n => tlsOk_upTo (h.tls ht n), h.body⟩
  · rcases Nat.lt_or_ge n N with hn | hn
    · rw [XI.upTo_at_lt hn]; exact h.calls n hn
    · exact calleeOkGP_upTo_ge hn h.pc
  · rcases Nat.lt_or_ge n N with hn | hn
    · rw [XI.upTo_at_lt hn]; exact h.tries ht n hn
    · exact calleeTryOkGP_upTo_ge hn

/-- The guarded paired semantics of `XI.upTo N` agrees with `XI`'s at the counters `j < N` and
on the non-calls. -/
theorem pairSemD_upTo_eq (gv : Nat → String → Prop) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (XI : ExtSemI) {N j : Nat} {i : MInst} (h : j < N ∨ i.isCallI = false) :
    pairSemD (csemV gv F ctx ((XI.upTo N).at j)) F ctx ((XI.upTo N).at j) i =
      pairSemD (csemV gv F ctx (XI.at j)) F ctx (XI.at j) i := by
  rcases h with h | h
  · rw [XI.upTo_at_lt h]
  · have e := csemVI_upTo_eq gv F ctx XI (N := N) (j := j) (Or.inr h)
    funext us p
    have hg : PGuard F ctx ((XI.upTo N).at j) i us p ↔ PGuard F ctx (XI.at j) i us p :=
      ⟨fun ⟨Y, a, b, c, d⟩ => ⟨Y, a, b, rdOk_X c, rdOk_X d⟩,
        fun ⟨Y, a, b, c, d⟩ => ⟨Y, a, b, rdOk_X c, rdOk_X d⟩⟩
    by_cases hp : PGuard F ctx (XI.at j) i us p
    · rw [pairSemD_of (hg.2 hp), pairSemD_of hp]
      simp only [pairSem, e]
    · simp [pairSemD, hp, mt hg.1 hp]

/-- **The paired run to counter `≤ N` is one of `XI.upTo N`.** -/
theorem vstar_pairDI_upTo {vc : VCode} {gv : Nat → String → Prop} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {XI : ExtSemI} {N : Nat} {v v' : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    (h : Star (VStep vc (pairDI (csemV gv F ctx) F ctx XI)) v v') (hN : vctr v' ≤ N) :
    Star (VStep vc (pairDI (csemV gv F ctx) F ctx (XI.upTo N))) v v' :=
  vstar_counted_upTo (sem := fun n => pairSemD (csemV gv F ctx (XI.at n)) F ctx (XI.at n))
    (sem' := fun n => pairSemD (csemV gv F ctx ((XI.upTo N).at n)) F ctx ((XI.upTo N).at n))
    (fun _ _ h => (pairSemD_upTo_eq gv F ctx XI h).symm) h hN

/-- **A step of the paired semantics of `XI.upTo N` is one of `XI`.** -/
theorem pairDI_upTo_sub {gv : Nat → String → Prop} {F : BitVec 64 → Prop} {ctx : FnCtx}
    {XI : ExtSemI} {N : Nat} {i : MInst} {us : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {r : List CV × ((Arm.ArmState × Arm.ArmState) × Nat) × Ctl}
    (h : pairDI (csemV gv F ctx) F ctx (XI.upTo N) i us w = some r) :
    pairDI (csemV gv F ctx) F ctx XI i us w = some r := by
  cases hc : i.isCallI with
  | false =>
    simp only [pairDI, ISem.counted] at h ⊢
    rw [← pairSemD_upTo_eq gv F ctx XI (N := N) (j := w.2) (Or.inr hc)]
    exact h
  | true =>
    rcases Nat.lt_or_ge w.2 N with hn | hn
    · simp only [pairDI, ISem.counted] at h ⊢
      rw [← pairSemD_upTo_eq gv F ctx XI (N := N) (j := w.2) (Or.inl hn)]
      exact h
    · exfalso
      simp only [pairDI, ISem.counted, Option.map_eq_some_iff] at h
      obtain ⟨r', h1, -⟩ := h
      obtain ⟨-, h2⟩ := pairSemD_sub h1
      rw [XI.upTo_at_ge hn] at h2
      simp only [pairSem] at h2
      rw [csemV_noCall_call hc] at h2
      cases h2

theorem VStep.pairDI_upTo {vc : VCode} {gv : Nat → String → Prop} {F : BitVec 64 → Prop}
    {ctx : FnCtx} {XI : ExtSemI} {N : Nat} {v v' : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    (h : VStep vc (pairDI (csemV gv F ctx) F ctx (XI.upTo N)) v v') :
    VStep vc (pairDI (csemV gv F ctx) F ctx XI) v v' :=
  VStep.sub (fun _ _ _ _ h => pairDI_upTo_sub h) h

/-- **A counted run from counter `≤ N` to counter `> N` passes the step from counter `N`.** -/
theorem vstar_split_ctr {V W : Type} {vc : VCode} {sem : Nat → ISem V W} {N : Nat}
    {v v' : VConf V (W × Nat)} (h : Star (VStep vc (ISem.counted sem)) v v') (h0 : vctr v ≤ N)
    (h1 : N < vctr v') :
    ∃ x y, Star (VStep vc (ISem.counted sem)) v x ∧ VStep vc (ISem.counted sem) x y ∧
      Star (VStep vc (ISem.counted sem)) y v' ∧ vctr x = N ∧ N < vctr y := by
  induction h with
  | refl => omega
  | @step v1 v2 v3 hs h23 ih =>
    by_cases hv2 : vctr v2 ≤ N
    · obtain ⟨x, y, hx, hxy, hy, hxN, hyN⟩ := ih hv2 h1
      exact ⟨x, y, .step hs hx, hxy, hy, hxN, hyN⟩
    · have hle : vctr v2 ≤ vctr v1 + 1 := by
        cases hs with
        | @step b k ρ w vb i ops outs w' ctl c' hvb hi hops hsem hlen hn =>
          have hcc := vnext_ctr hn
          obtain ⟨-, hw⟩ := ISem.counted_some hsem
          show _ ≤ w.2 + 1
          rw [hcc, hw]; split <;> omega
      exact ⟨v1, v2, .refl _, hs, h23, by omega, by omega⟩

/-- **`pstar_of_projS` with the pair guard in a larger semantics.** -/
theorem pstar_of_projSB {V W W₁ : Type} {vc : VCode} {semD semD' : ISem V W}
    {sem₁ sem₂ : ISem V W₁} {π₁ π₂ : W → W₁}
    (hsub : ∀ a b, VStep vc semD a b → VStep vc semD' a b)
    (h₁ : ISem.ProjW π₁ semD sem₁) (h₂ : ISem.ProjW π₂ semD sem₂) {c x : VConf V W}
    (h : Star (VStep vc semD) c x) (hx : ∃ y, VStep vc semD' x y) :
    Star (PStep vc sem₁ sem₂ (PairOfG π₁ π₂ (StepOrRet vc semD')))
      (c.mapW π₁, c.mapW π₂) (x.mapW π₁, x.mapW π₂) := by
  induction h with
  | refl => exact .refl _
  | @step a b _ hs rest ih =>
    have hb : ∃ y, VStep vc semD' b y := by
      cases rest with
      | refl => exact hx
      | step h1 _ => exact ⟨_, hsub _ _ h1⟩
    exact .step ⟨VStep_mapW h₁ hs, VStep_mapW h₂ hs, VConf.sameAt_mapW π₁ π₂ b, b, rfl, rfl,
      .inl hb⟩ (ih hx)

end E2E
