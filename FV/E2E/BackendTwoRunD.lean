import FV.E2E.BackendPairRunD
import FV.E2E.RegLevelTwoRunS

/-!
# Two activations along one CLIF run, the reads of the pair run guarded (SEM1 #537, #699)

`backend_twoRunPRIYS` without its world-read guard premise `hGdP`: the paired run comes from
`backend_pairRunD` (every step guarded by the difference set, `pairSemD`), and the guard is
handed to the lock premises through the pair invariant: `hK` receives, besides the two
configurations being projections of one paired configuration, that every unguarded paired step
from it is a guarded one (`GuardedAt`). Each activation's own semantics is the unguarded one
(`Ok := (· = F)`, `csemVGS_eqF`); the difference-set guard is a property of the pair, so the
lock-step (`hG`, `hstep`) reads it from the pair facts `KJ` that `hK` builds.

* `VStep.sub`, `GuardedAt`, `guardedAt_of_step`, `guardedAt_ret`, `PairOfG`,
  `pstar_of_projG`;
* `pairDI_sub`, `pairFst_projD`, `pairSnd_projD`;
* **`backend_twoRunPRIYD`**.
-/

namespace Backend.Proof

open Backend E2E

section
variable {V W W₁ : Type} {vc : VCode}

theorem VStep.sub {sem sem' : ISem V W} (hsub : ∀ i us w r, sem i us w = some r → sem' i us w = some r)
    {c c' : VConf V W} (h : VStep vc sem c c') : VStep vc sem' c c' := by
  cases h with
  | step hvb hi hops hsem hlen hn => exact VStep.step hvb hi hops (hsub _ _ _ _ hsem) hlen hn

/-- **Every step of `semU` from `c` is one of `semD`.** -/
def GuardedAt (vc : VCode) (semU semD : ISem V W) (c : VConf V W) : Prop :=
  ∀ c', VStep vc semU c c' → VStep vc semD c c'

theorem guardedAt_of_step {semU semD : ISem V W}
    (hsub : ∀ i us w r, semD i us w = some r → semU i us w = some r) {c d : VConf V W}
    (h : VStep vc semD c d) : GuardedAt vc semU semD c := by
  intro c' h'
  have e := vstep_det (VStep.sub hsub h) h'
  subst e
  exact h

theorem guardedAt_ret {semU semD : ISem V W} (vals : List V) (w : W) :
    GuardedAt vc semU semD (.ret vals w) := fun _ h => by cases h

/-- The start of a run with a further step has a step. -/
theorem star_head_step {sem : ISem V W} {c x y : VConf V W} (h : Star (VStep vc sem) c x)
    (hy : VStep vc sem x y) : ∃ z, VStep vc sem c z := by
  cases h with
  | refl => exact ⟨_, hy⟩
  | step h1 _ => exact ⟨_, h1⟩

/-- **Two configurations are the projections of one paired configuration satisfying `G`.** -/
def PairOfG (π₁ π₂ : W → W₁) (G : VConf V W → Prop) (x x' : VConf V W₁) : Prop :=
  ∃ c : VConf V W, x = c.mapW π₁ ∧ x' = c.mapW π₂ ∧ G c

/-- **A run of `semD` with a further step is a run of pair steps of the projections**, every
configuration of it guarded. -/
theorem pstar_of_projG {semU semD : ISem V W} {sem₁ sem₂ : ISem V W₁} {π₁ π₂ : W → W₁}
    (hsub : ∀ i us w r, semD i us w = some r → semU i us w = some r)
    (h₁ : ISem.ProjW π₁ semD sem₁) (h₂ : ISem.ProjW π₂ semD sem₂) {c x : VConf V W}
    (h : Star (VStep vc semD) c x) (hx : ∃ y, VStep vc semD x y) :
    Star (PStep vc sem₁ sem₂ (PairOfG π₁ π₂ (GuardedAt vc semU semD)))
      (c.mapW π₁, c.mapW π₂) (x.mapW π₁, x.mapW π₂) := by
  induction h with
  | refl => exact .refl _
  | @step a b _ hs rest ih =>
    have hb : ∃ y, VStep vc semD b y := by
      cases rest with
      | refl => exact hx
      | step h1 _ => exact ⟨_, h1⟩
    obtain ⟨y, hy⟩ := hb
    exact .step ⟨VStep_mapW h₁ hs, VStep_mapW h₂ hs, VConf.sameAt_mapW π₁ π₂ b, b, rfl, rfl,
      guardedAt_of_step hsub hy⟩ (ih hx)

end

end Backend.Proof

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

theorem pairDI_sub {sem : ExtSem → Sem} {F : BitVec 64 → Prop} {ctx : FnCtx} {XI : ExtSemI}
    {i : MInst} {us : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {r : List CV × ((Arm.ArmState × Arm.ArmState) × Nat) × Ctl}
    (h : pairDI sem F ctx XI i us w = some r) :
    ISem.counted (fun n => pairSem (sem (XI.at n))) i us w = some r := by
  simp only [pairDI, ISem.counted, Option.map_eq_some_iff] at h ⊢
  obtain ⟨r', h1, h2⟩ := h
  exact ⟨r', (pairSemD_sub h1).2, h2⟩

theorem pairFst_projD (sem : ExtSem → Sem) (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) :
    ISem.ProjW pairFst (pairDI sem F ctx XI) (ISem.counted fun n => sem (XI.at n)) :=
  fun _ _ _ _ _ _ h => pairFst_proj (fun n => sem (XI.at n)) _ _ _ _ _ _ (pairDI_sub h)

theorem pairSnd_projD (sem : ExtSem → Sem) (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) :
    ISem.ProjW pairSnd (pairDI sem F ctx XI) (ISem.counted fun n => sem (XI.at n)) :=
  fun _ _ _ _ _ _ h => pairSnd_proj (fun n => sem (XI.at n)) _ _ _ _ _ _ (pairDI_sub h)

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 4000000 in
/-- **Two activations of a compiled function along one returning CLIF run, the pair run
guarded** (module doc): `backend_twoRunPRIYS` at `Ok := (· = F)` without `hGdP`; `hK` receives
the guard of the paired configuration (`GuardedAt`: every unguarded paired step from it reads
outside a set containing `F` and the bytes where the two worlds differ). -/
theorem backend_twoRunPRIYD (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
        (prologueLines R.af.saves R.af.frameSize).length R.s0) (.reg r)) e x →
      Match ckc ins ckeep (fun r => locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } :
        RL).step (prologueLines R.af.saves R.af.frameSize).length t0) (.reg r)) e' x' →
      PairOfG pairFst pairSnd (GuardedAt vcp
        (ISem.counted fun n => pairSem (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩ (XI.at n)))
        (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)) x x' →
      KJ (e.mapW Prod.fst) (e'.mapW Prod.fst))
    (hpro : LB
      (MConf.init R.rf (locVal R.fr (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize).length R.s0)) w₀)
      (MConf.init R.rf (locVal R.fr (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize).length t0)) w₀')
      (iterN ({ R with X := XI.at 0 } : RL).step (prologueLines R.af.saves R.af.frameSize).length R.s0)
      (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueLines R.af.saves R.af.frameSize).length t0)) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ N e e',
      (∀ i < (prologueLines R.af.saves R.af.frameSize).length,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)) ∧
      (∀ i < N, ∃ c c' j, Lk c c' j
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize).length + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + i) t0)) ∧
      JR R ({ R with s0 := t0, G := G' } : RL) KJ LB
        (iterN ({ R with X := XI.at 0 } : RL).step ((prologueLines R.af.saves R.af.frameSize).length + N) R.s0) e
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize).length + N) t0) e' ∧
      (∀ i < R.retLen,
        ({ R with X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with X := XI.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize).length + N + i) R.s0) ∧
        ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).GoodXNY (fun _ => True)
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
            ((prologueLines R.af.saves R.af.frameSize).length + N + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize).length + N + R.retLen) t0) = ra' := by
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
  have hsubD : ∀ i us w r,
      pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI i us w = some r →
      ISem.counted (fun n => pairSem (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩ (XI.at n))) i us w =
        some r := fun _ _ _ _ h => pairDI_sub h
  subst hR
  have hy : PStep _ _ _ (PairOfG pairFst pairSnd (GuardedAt vcp _ _)) _ _ :=
    (⟨VStep_mapW hp₁ hlast, VStep_mapW hp₂ hlast, VConf.sameAt_mapW pairFst pairSnd (.ret outs w),
      .ret outs w, rfl, rfl, guardedAt_ret outs w⟩ :
      PStep vcp _ _ (PairOfG pairFst pairSnd (GuardedAt vcp
        (ISem.counted fun n => pairSem (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩ (XI.at n)))
        (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)))
        ((VConf.run ⟨b, kk, ρ, w₁⟩).mapW pairFst, (VConf.run ⟨b, kk, ρ, w₁⟩).mapW pairSnd)
        ((VConf.ret outs w).mapW pairFst, (VConf.ret outs w).mapW pairSnd))
  have hpp := pstar_of_projG hsubD hp₁ hp₂ hs ⟨_, hlast⟩
  have hg0 : GuardedAt vcp
      (ISem.counted fun n => pairSem (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩ (XI.at n)))
      (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
      (.run ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩) :=
    let ⟨_, h0⟩ := star_head_step hs hlast
    guardedAt_of_step hsubD h0
  exact RL.twoRunPRS hc.check hc.alloc hc.emit hc.layout hlm hpsF he he' rfl hcov ρ₀
    (fun _ Y => Y = F) (fun _ Y => Y = F) KJ LB OkS OkS' hG hG' Lk hLpc hstart hstep hend hK hpro
    hpp ⟨VConf.init ρ₀ ((w₀, w₀'), 0), rfl, rfl, hg0⟩
    ⟨.run ⟨b, kk, ρ, w₁⟩, rfl, rfl, guardedAt_of_step hsubD hlast⟩ hy

end

end E2E
