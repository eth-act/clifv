import FV.E2E.BackendTwoRun
import FV.E2E.RegLevelTwoRunS

/-!
# Two activations along one CLIF run, reads-only guard (SEM1 #537, #699)

`backend_twoRunPRIY` with the world-read guard `hGdP` on `csemVGS` (`RegLevelCorrectCYS.lean`:
stores are admitted whatever the guard set, only reads must avoid it), ending in `RL.twoRunPRS`.
The guard premise is weaker than `backend_twoRunPRIY`'s (`csemVGS_of_csemVG`); with the
lock-step's `Ok w Y := Y = Zof F D cm` it no longer fails at every store into an uninitialised
byte of `D` (#699).

* **`backend_twoRunPRIYS`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 4000000 in
/-- **Two activations of a compiled function along one returning CLIF run, reads-only guard**
(`backend_twoRunPRIY`'s statement on `csemVGS`/`RL.semGS`; same proof). -/
theorem backend_twoRunPRIYS (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
    (OkG : Arm.ArmState → (BitVec 64 → Prop) → Prop)
    (hGdP : ∀ us outs w, VRetFrom vcp
        (ISem.counted fun n => pairSem (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩ (XI.at n)))
        ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w →
      VRetFrom vcp
        (ISem.counted fun n => pairSem (csemVGS (GotV vcp) F ⟨fa.k, af.slotBase⟩ (XI.at n) OkG))
        ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w)
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
      MStep R.vc (({ R with X := XI.at n } : RL).semGS OkG) ckeep R.rf c d →
      MStep R.vc (({ R with X := XI.at n } : RL).semGS (OkS c c')) ckeep R.rf c d)
    (hG' : ∀ n c c' d, KJ c c' →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI.at n } : RL).semGS OkG) ckeep R.rf c' d →
      MStep R.vc (({ R with s0 := t0, G := G', X := XI.at n } : RL).semGS (OkS' c c')) ckeep R.rf
        c' d)
    (Lk : MConf CV Arm.ArmState → MConf CV Arm.ArmState → Nat → Arm.ArmState → Arm.ArmState → Prop)
    (hLpc : ∀ c c' i u u', Lk c c' i u u' → Arm.r .PC u = Arm.r .PC u')
    (hstart : ∀ c c' s s', KJ c c' → LB c c' s s' → Lk c c' 0 s s')
    (hstep : ∀ n n' c c' i u u', KJ c c' →
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
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0) (.reg r)) e x →
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } :
        RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0) (.reg r)) e' x' →
      PairOf pairFst pairSnd x x' → KJ (e.mapW Prod.fst) (e'.mapW Prod.fst))
    (hpro : LB
      (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)) w₀)
      (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0)) w₀')
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length t0)) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ N e e',
      (∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)) ∧
      (∀ i < N, ∃ c c' j, Lk c c' j
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) KJ LB
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N) R.s0) e
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N) t0) e' ∧
      (∀ i < R.retLen,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + i) R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + N + R.retLen) t0) = ra' := by
  intro vals cm hrun
  obtain ⟨us, outs, w, hv, -⟩ := vcode_niIG hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce hrel hrel'
    hargs hsw hreg hstk htr fuel vals cm hrun
  have hP := (prep_soundW (DriverSemG.countedW fun n => driverSemG_pair F ⟨fa.k, af.slotBase⟩ (XI.at n))
    hc.prepOk ρ₀ ((w₀, w₀'), 0)).1 _ _ _ hv
  obtain ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hk, hops, hvals, hsem⟩ :=
    hGdP _ _ _ (vRetFrom_gotVP hP)
  have hRF : R.F = F := by subst hR; exact he.hF
  have hRF' : ({ R with s0 := t0, G := G' } : RL).F = F := by subst hR; exact he'.hF
  have hRgv : R.gv = GotV vcp := by subst hR; rfl
  have hRvc : R.vc = vcp := by subst hR; rfl
  have hRctx : R.ctx = ⟨fa.k, af.slotBase⟩ := by subst hR; rfl
  have hp₁ : ISem.ProjW pairFst
      (ISem.counted fun n => pairSem (csemVGS (GotV vcp) F ⟨fa.k, af.slotBase⟩ (XI.at n) OkG))
      (csemVIGS R.gv R.F R.ctx XI OkG) := by
    rw [hRF, hRgv, hRctx]; exact pairFst_proj _
  have hp₂ : ISem.ProjW pairSnd
      (ISem.counted fun n => pairSem (csemVGS (GotV vcp) F ⟨fa.k, af.slotBase⟩ (XI.at n) OkG))
      (csemVIGS R.gv ({ R with s0 := t0, G := G' } : RL).F R.ctx XI OkG) := by
    rw [hRF', hRgv, hRctx]; exact pairSnd_proj _
  have hck : ctlCheck vcp rf = true := (lowerRFunc_ok hc.alloc).2.2
  obtain ⟨ns, rfl⟩ := ctlCheck_rets hck hvb hk
  rw [operands_retsC] at hops
  cases hops
  have hlast : VStep vcp
      (ISem.counted fun n => pairSem (csemVGS (GotV vcp) F ⟨fa.k, af.slotBase⟩ (XI.at n) OkG))
      (.run ⟨b, kk, ρ, w₁⟩) (.ret outs w) := by
    obtain ⟨hsP, -⟩ := ISem.counted_some hsem
    obtain ⟨hs1, -⟩ := pairSem_inv hsP
    have hsem' := (csemVGS_inv hs1).2
    simp only [csemV, csem, Option.some.injEq, Prod.mk.injEq] at hsem'
    obtain ⟨rfl, -, -⟩ := hsem'
    rw [hvals] at hsem ⊢
    refine VStep.step hvb hk (operands_retsC ns) hsem ?_ (VNext.ret rfl)
    rw [List.toList_toArray, filter_isDef_retOpsC]; rfl
  subst hR
  have hy := pstep_of_proj hp₁ hp₂ hlast
  have hpp := pstar_of_proj hp₁ hp₂ hs
  exact RL.twoRunPRS hc.check hc.alloc hc.emit hc.layout hlm hpsF he he' rfl hcov ρ₀ OkG OkG KJ LB
    OkS OkS' hG hG' Lk hLpc hstart hstep hend hK hpro hpp
    ⟨VConf.init ρ₀ ((w₀, w₀'), 0), rfl, rfl⟩ ⟨.run ⟨b, kk, ρ, w₁⟩, rfl, rfl⟩ hy

end

end E2E
