import FV.E2E.PairDriverID
import FV.E2E.BackendTwoRun

/-!
# The guarded paired run through prepare and the GOT guard (SEM1 #537, #699, item (1))

`vcode_niID`'s paired counted run of the selected code, carried to the allocated code as
`backend_twoRunPRIY` carries the unguarded one: `prepare` (`prep_soundW` with
`DriverSemG.countedW` of `driverSemG_pairD`) and the GOT guard (`gotInvPD_star`, the guard of
`pairSemD` does not see the semantics' GOT check). This discharges the world-read guard premise
of the pair run in its paired form: every step of the returning paired run of `vcp` reads
outside a set containing `F` and every byte where the two worlds differ.

* `gotInvPD_step`, `gotInvPD_star`, `vRetFrom_gotVPD`;
* **`backend_pairRunD`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {vc : VCode} {F : BitVec 64 → Prop} {ctx : FnCtx} {XI : ExtSemI}

/-- The counted guarded paired family of `sem`. -/
noncomputable abbrev pairDI (sem : ExtSem → Sem) (F : BitVec 64 → Prop) (ctx : FnCtx)
    (XI : ExtSemI) : ISem CV ((Arm.ArmState × Arm.ArmState) × Nat) :=
  ISem.counted fun n => pairSemD (sem (XI.at n)) F ctx (XI.at n)

/-- **One counted guarded paired step** keeps the GOT invariant and is a step of the guarded
paired `csemV`. -/
theorem gotInvPD_step {s : VState CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    {c' : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)} (hI : GotInvP vc XI s)
    (h : VStep vc (pairDI (csem F ctx) F ctx XI) (.run s) c') :
    VStep vc (pairDI (csemV (GotV vc) F ctx) F ctx XI) (.run s) c' ∧
      ∀ s', c' = .run s' → GotInvP vc XI s' := by
  obtain ⟨b, k, ρ, ⟨⟨w, w'⟩, m⟩⟩ := s
  cases h with
  | @step _ _ _ _ vb i ops outs w₂ ctl _ hvb hi hops hsem hlen hnext =>
  obtain ⟨hs, -⟩ := ISem.counted_some hsem
  obtain ⟨hg, -⟩ := pairSemD_sub hs
  have hsemU : ISem.counted (fun n => pairSem (csem F ctx (XI.at n))) i (vuses ops ρ) ((w, w'), m) =
      some (outs, w₂, ctl) := by
    simp only [pairDI, ISem.counted, pairSemD_of hg] at hsem ⊢
    exact hsem
  obtain ⟨hU, hinv⟩ := gotInvP_step (F := F) (ctx := ctx) hI (VStep.step hvb hi hops hsemU hlen hnext)
  refine ⟨?_, hinv⟩
  cases hU with
  | step hvb2 hi2 hops2 hsem2 hlen2 hnext2 =>
    rw [hvb] at hvb2; cases hvb2
    rw [hi] at hi2; cases hi2
    rw [hops] at hops2; cases hops2
    refine VStep.step hvb hi hops ?_ hlen2 hnext2
    simp only [pairDI, ISem.counted, pairSemD_of hg] at hsem2 ⊢
    exact hsem2

theorem gotInvPD_star {s s' : VState CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    (hI : GotInvP vc XI s)
    (h : Star (VStep vc (pairDI (csem F ctx) F ctx XI)) (.run s) (.run s')) :
    Star (VStep vc (pairDI (csemV (GotV vc) F ctx) F ctx XI)) (.run s) (.run s') ∧
      GotInvP vc XI s' := by
  generalize ha : (VConf.run s : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)) = a at h
  generalize hb : (VConf.run s' : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)) = b at h
  induction h generalizing s with
  | refl => subst ha; cases hb; exact ⟨.refl _, hI⟩
  | @step a1 a2 a3 h1 h2 ih =>
    subst ha
    cases a2 with
    | run s2 =>
      obtain ⟨h1', hI2⟩ := gotInvPD_step hI h1
      obtain ⟨h2', hI'⟩ := ih (hI2 s2 rfl) rfl hb
      exact ⟨.step h1' h2', hI'⟩
    | ret vals w => subst hb; cases h2 with | step h _ => cases h
    | halt w => subst hb; cases h2 with | step h _ => cases h

/-- **A returning counted guarded paired run of `csem` is one of `csemV (GotV vc)`.** -/
theorem vRetFrom_gotVPD {ρ₀ : Nat → CV} {w₀ : (Arm.ArmState × Arm.ArmState) × Nat}
    {us : List (Reg × Reg)} {vals : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    (h : VRetFrom vc (pairDI (csem F ctx) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ us vals w) :
    VRetFrom vc (pairDI (csemV (GotV vc) F ctx) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  obtain ⟨hs', -⟩ := gotInvPD_star
    (show GotInvP vc XI ⟨0, 0, ρ₀, w₀⟩ from gotInv_entry vc (XI.at 0) ρ₀ w₀.1.1) hs
  refine ⟨b, k, ρ, w₁, vb, ops, outs, hs', hvb, hk, hops, hvals, ?_⟩
  have hnc : ∀ info, ((MInst.rets us) = .call info ∨ ∃ ti, (MInst.rets us) = .tryCall info ti) →
      gotGuard (GotV vc) (XI.at w₁.2) info vals := fun info h => by
    rcases h with h | ⟨_, h⟩ <;> cases h
  have e : pairSemD (csemV (GotV vc) F ctx (XI.at w₁.2)) F ctx (XI.at w₁.2) (.rets us) vals w₁.1 =
      pairSemD (csem F ctx (XI.at w₁.2)) F ctx (XI.at w₁.2) (.rets us) vals w₁.1 := by
    rw [pairSemD_of (pGuard_noLoad rfl _ _), pairSemD_of (pGuard_noLoad rfl _ _)]
    simp only [pairSem, csemV_eq hnc]
  show (pairSemD (csemV (GotV vc) F ctx (XI.at w₁.2)) F ctx (XI.at w₁.2) (.rets us) vals w₁.1).map _ = _
  rw [e]
  exact hsem

end

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- **The paired run of the allocated code, reads guarded by the difference set**: from two
body-entry worlds related to the CLIF entry and agreeing outside `F ∪ D` (`vcode_niIG`'s
premises), a returning CLIF run gives a returning paired counted run of `vcp` in the guarded
paired semantics of `csemV (GotV vcp)`, final worlds agreeing outside `F ∪ D`. -/
theorem backend_pairRunD (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hNI : ∀ s n, ReachN env p cs s n → XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f)) (XI.at n))
    (hTls : ∀ n, XTls F (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem
      w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w,
        VRetFrom vcp (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 := by
  intro vals cm hrun
  obtain ⟨us, outs, w, hv, hsw'⟩ := vcode_niID hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce hrel
    hrel' hargs hsw hreg hstk htr fuel vals cm hrun
  have hP := (prep_soundW (DriverSemG.countedW fun n => driverSemG_pairD F ⟨fa.k, af.slotBase⟩ (XI.at n))
    hc.prepOk ρ₀ ((w₀, w₀'), 0)).1 _ _ _ hv
  exact ⟨us, outs, w, vRetFrom_gotVPD hP, hsw'⟩

end

end E2E
