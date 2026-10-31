import FV.E2E.BackendTwoRunD
import FV.E2E.RegLevelTwoRunT

/-!
# Two activations along one CLIF run, the lock step told where it is (SEM1 #537)

`backend_twoRunPRIYD` on `RL.twoRunPRT`: the lock-step obligation `hstep` also receives, for both
runs, that the state is the `i`-th state of the segment realising the step of the configuration,
strictly before its end (`RL.InSeg`), and `hK` receives that the paired configuration has a
guarded step or is the return (`StepOrRet`; `GuardedAt` follows, `guardedAt_of_step`): the lock
needs the paired step's guard at the instruction of the configuration. Same proof otherwise.

* `StepOrRet`, `pstar_of_projS`;
* **`backend_twoRunPRIYT`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {V W W₁ : Type} {vc : VCode}

/-- **`c` has a step of `sem`, or is a return.** -/
def StepOrRet (vc : VCode) (sem : ISem V W) (c : VConf V W) : Prop :=
  (∃ y, VStep vc sem c y) ∨ ∃ vals w, c = .ret vals w

/-- **A run of `semD` with a further step is a run of pair steps of the projections**, every
configuration of it with a step (`pstar_of_projG` with `StepOrRet`). -/
theorem pstar_of_projS {semD : ISem V W} {sem₁ sem₂ : ISem V W₁} {π₁ π₂ : W → W₁}
    (h₁ : ISem.ProjW π₁ semD sem₁) (h₂ : ISem.ProjW π₂ semD sem₂) {c x : VConf V W}
    (h : Star (VStep vc semD) c x) (hx : ∃ y, VStep vc semD x y) :
    Star (PStep vc sem₁ sem₂ (PairOfG π₁ π₂ (StepOrRet vc semD)))
      (c.mapW π₁, c.mapW π₂) (x.mapW π₁, x.mapW π₂) := by
  induction h with
  | refl => exact .refl _
  | @step a b _ hs rest ih =>
    have hb : ∃ y, VStep vc semD b y := by
      cases rest with
      | refl => exact hx
      | step h1 _ => exact ⟨_, h1⟩
    exact .step ⟨VStep_mapW h₁ hs, VStep_mapW h₂ hs, VConf.sameAt_mapW π₁ π₂ b, b, rfl, rfl,
      .inl hb⟩ (ih hx)

end

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunPRIYD` with the segment positions handed to the lock step.** -/
theorem backend_twoRunPRIYT (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
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
    (htr : TrapsExplicit env p cs) (fuel : Nat)
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {H : ArmHooks} {G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀)
    (he' : ActEntryPR vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀')
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc)
    (KJ : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Prop)
    (LB : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Arm.ArmState → Arm.ArmState → Prop)
    (OkS OkS' : MConf CV Arm.ArmState → MConf CV Arm.ArmState →
      Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hG : ∀ n c c' d, KJ c c' →
      MStep R.vc (({ R with X := XI.at n } : RL).semGS (fun _ Y => Y = F)) ckeep R.rf c d →
      MStep R.vc (({ R with X := XI.at n } : RL).semGS (OkS c c')) ckeep R.rf c d)
    (hG' : ∀ n c c' d, KJ c c' →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI.at n } : RL).semGS (fun _ Y => Y = F))
        ckeep R.rf c' d →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI.at n } : RL).semGS (OkS' c c')) ckeep R.rf
        c' d)
    (Lk : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Nat → Arm.ArmState → Arm.ArmState → Prop)
    (hLpc : ∀ c c' i u u', Lk c c' i u u' → Arm.r .PC u = Arm.r .PC u')
    (hstart : ∀ c c' s s', KJ c c' → LB c c' s s' → Lk c c' 0 s s')
    (hstep : ∀ n n' c c' i u u', KJ c c' →
      ({ R with X := XI.at n } : RL).InSeg (OkS c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkS' c c') c' i u' →
      (({ R with X := XI.at n } : RL).GoodX u ∧
        ({ R with X := XI.at n } : RL).WReadsIn (OkS c c') u) →
      (({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' ∧
        ({ R with s0 := t0, G := G', X := XI.at n' } : RL).WReadsIn (OkS' c c') u') →
      Lk c c' i u u' → Lk c c' (i + 1) (({ R with X := XI.at 0 } : RL).step u)
        (({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step u'))
    (hend : ∀ c c' d d' i u u', KJ c c' → KJ d d' → MConf.ShapeEq d d' →
      (∃ W : Nat × PState × List Line, QWA R u W.1 W.2.1 W.2.2 d ∧
        QWA ({ R with s0 := t0, G := G' } : RL) u' W.1 W.2.1 W.2.2 d') →
      Lk c c' i u u' → LB d d' u u')
    (hK : ∀ (ckc : CheckCtx) (ins : Array (Option AState)) (a0 : AState),
      CheckedAt R.vc R.rf ckc ins a0 → ∀ e e' x x',
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0) (.reg r)) e x →
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } :
        RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0) (.reg r)) e' x' →
      PairOfG pairFst pairSnd (StepOrRet vcp
        (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)) x x' →
      KJ (e.mapW Prod.fst) (e'.mapW Prod.fst))
    (hpro : LB
      (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)) w₀)
      (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0)) w₀')
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) t0)) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ N e e',
      (∀ i < (prologueSteps R.af.saves R.af.frameSize R.af.isCaller),
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)) ∧
      (∀ i < N, ∃ c c' j, Lk c c' j
        (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) KJ LB
        (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) R.s0) e
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) t0) e' ∧
      (∀ i < R.retLen,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step
            (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + i) R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
            (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) t0) = ra' ∧
      R.RetsAt e ∧ R.RetsAt e' := by
  intro vals cm hrun
  obtain ⟨us, outs, w, hv, -⟩ := backend_pairRunD hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce
    hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
  obtain ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hk, hops, hvals, hsem⟩ := hv
  have hRF : R.F = F := by subst hR; exact he.hF
  have hRF' : ({ R with s0 := t0, G := G' } : RL).F = F := by subst hR; exact he'.hF
  have hRgv : R.gv = GotV vcp := by subst hR; rfl
  have hRctx : R.ctx = ⟨fa.k, af.slotBase⟩ := by subst hR; rfl
  have hp₁ : ISem.ProjW pairFst
      (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
      (csemVIGS R.gv R.F R.ctx XI (fun _ Y => Y = F)) := by
    rw [hRF, csemVIGS_eqF, hRgv, hRctx]; exact pairFst_projD _ _ _ _
  have hp₂ : ISem.ProjW pairSnd
      (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
      (csemVIGS R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI
        (fun _ Y => Y = F)) := by
    rw [hRF', csemVIGS_eqF, hRgv, hRctx]; exact pairSnd_projD _ _ _ _
  have hck : ctlCheck vcp rf = true := (lowerRFunc_ok hc.alloc).2.2
  obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hk
  rw [operands_retsC] at hops
  cases hops
  have hlast : VStep vcp
      (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
      (.run ⟨b, kk, ρ, w₁⟩) (.ret outs w) := by
    obtain ⟨hsP, -⟩ := ISem.counted_some hsem
    obtain ⟨-, hs1⟩ := pairSemD_sub hsP
    obtain ⟨hs1, -⟩ := pairSem_inv hs1
    have hsem' := hs1
    simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, -, -⟩ := hsem'
    rw [hvals] at hsem ⊢
    refine VStep.step hvb hk (operands_retsC ns) hsem ?_ (VNext.ret rfl)
    rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
  subst hR
  have hy : PStep _ _ _ (PairOfG pairFst pairSnd (StepOrRet vcp _)) _ _ :=
    (⟨VStep_mapW hp₁ hlast, VStep_mapW hp₂ hlast, VConf.sameAt_mapW pairFst pairSnd (.ret outs w),
      .ret outs w, rfl, rfl, .inr ⟨outs, w, rfl⟩⟩ :
      PStep vcp _ _ (PairOfG pairFst pairSnd (StepOrRet vcp
        (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)))
        ((VConf.run ⟨b, kk, ρ, w₁⟩).mapW pairFst, (VConf.run ⟨b, kk, ρ, w₁⟩).mapW pairSnd)
        ((VConf.ret outs w).mapW pairFst, (VConf.ret outs w).mapW pairSnd))
  have hpp := pstar_of_projS hp₁ hp₂ hs ⟨_, hlast⟩
  exact RL.twoRunPRT hc.check hc.alloc hc.emit hc.layout hlm hpsF he he' rfl hcov ρ₀
    (fun _ Y => Y = F) (fun _ Y => Y = F) KJ LB OkS OkS' hG hG' Lk hLpc hstart hstep hend hK hpro
    hpp ⟨VConf.init ρ₀ ((w₀, w₀'), 0), rfl, rfl, .inl (star_head_step hs hlast)⟩
    ⟨.run ⟨b, kk, ρ, w₁⟩, rfl, rfl, .inl ⟨_, hlast⟩⟩ hy

end

end E2E
