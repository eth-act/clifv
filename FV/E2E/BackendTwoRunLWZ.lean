import FV.E2E.BackendTwoRunLW

/-!
# The per-index lock with its set (SEM1 #537, `docs/plans/uninit.md` §5.9, determinism step)

`backend_twoRunLERW` gives, at every index before the return, *some* set `Z` with
`StEqOutX Z`. The determinism step (`CallTwinC`, `DetRunPRBC`) needs what `Z` leaves out: the
callees' dead stack (`StackBelow R.K R.spB`, where the callee slot bytes of a call are,
`LinkSys.slotByte_eq_of_lock`). Every set of the proof is a lock set `R.Zc d d'` (prologue: of the
initial configurations, body: of the paired configurations, epilogue: of the `rets`
configurations). So:

* **`backend_twoRunLERWZ`**: `backend_twoRunLERW` (same premises and proof) with the per-index
  clause `∃ d d', StEqOutX (R.Zc d d') …`;
* `RL.deadStack_eq_of_Zc`: states locked at `R.Zc d d'` agree on the dead stack.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **States locked at a lock set agree on the callees' dead stack.** -/
theorem RL.deadStack_eq_of_Zc {R : RL} {d d' : MConf CV Arm.ArmState} {u u' : Arm.ArmState}
    (h : StEqOutX (R.Zc d d') u u') {a : BitVec 64} (ha : StackBelow R.K R.spB a) :
    u.mem a = u'.mem a :=
  h.2.2 a fun hz => hz.2.2.1 ha

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 4000000 in
/-- **`backend_twoRunLERW` with the lock set at every index** (module doc). -/
theorem backend_twoRunLERWZ (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
    (hx30 : fa.x30Free lm = true)
    (hcall : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      ∀ x d, ({ R with X := XI.at n } : RL).AtLine u x → LineDest x d →
      StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ n n' c c' i u u', ({ R with X := XI.at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := XI.at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := XI.at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      (∃ a b c, ({ R with X := XI.at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hag : EntryAgree (frameDrop af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
    ∃ N,
      (∀ i < N, ∃ c c', StEqOutX (R.Zc c c')
        (iterN ({ R with X := XI.at 0 } : RL).step (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) R.s0)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + i) t0)) ∧
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) t0)
        (iterN ({ R with X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) t0).mem a =
        (iterN ({ R with X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + R.retLen) R.s0).mem a) ∧
      ∀ i < (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) + N + R.retLen, ∃ d d',
        StEqOutX (R.Zc d d') (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) := by
  intro vals cm hrun
  obtain ⟨N, e, e', hlk, ⟨⟨W, hqA, -⟩, -, -, hLB⟩, hpc, hpc', hre, hre'⟩ :=
    backend_twoRunLW hsub hc hone htc hX hNI hTls hsym hslot ρ₀ hce hrel hrel' hargs hsw hreg hstk
      htr fuel hlm hpsF he he' hR hcov hx30 hcall htls hag hx29 vals cm hrun
  refine ⟨N, hlk, hpc, hpc', ?_⟩
  have hs : ∀ (g : Arm.ArmState → Arm.ArmState) (x : Arm.ArmState) (j : Nat),
      iterN g (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N + j) x =
        iterN g j (iterN g (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + N) x) :=
    fun g x j => iterN_add ..
  subst hR
  have hF := he.hF
  subst hF
  obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hc.emit
  subst hk
  obtain ⟨ckc, ins, hck⟩ := checked_of_checkAlloc hc.check
  obtain ⟨a0, hat, hle⟩ := hck.at
  have hW0 : ({ actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp) with X := XI.at 0 } :
      RL).Wf :=
    ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, hc.alloc, hc.emit, hc.layout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack, ⟨body, hpsF⟩,
      he.abi.program, he.gfree⟩
  have hr1 : ∃ ms, e = .run ms := by
    obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hre; exact ⟨_, rfl⟩
  have hr2 : ∃ ms, e' = .run ms := by
    obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hre'; exact ⟨_, rfl⟩
  obtain ⟨hra, -, hm, hepi⟩ := RL.retLock_rets hW0 he.abi hx30 (QWA.qaX hqA hW0 he.abi) hre
    hLB.1.symm
  refine ⟨by rw [hs, hs]; exact hra, fun a hFa hDa => ?_, fun i hi => ?_⟩
  · rw [hs, hs]
    refine hm a ?_
    rintro ⟨-, -, -, hz⟩
    rcases hz with h | h
    · exact hFa h
    · rcases wDiff_of_wIn hr1 hr2 hLB.2.1 a h with h' | h'
      · exact hFa h'
      · exact hDa h'
  · have hPe : (prologueLines (actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)).af.saves
        (actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)).af.frameSize (actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)).af.isCaller).length
        = (prologueSteps af.saves af.frameSize af.isCaller) := rfl
    have hRe : (actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp)).retLen =
        ({ actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp) with X := XI.at 0 } : RL).retLen :=
      rfl
    rw [hPe] at hi hs
    rcases Nat.lt_or_ge i (prologueSteps af.saves af.frameSize af.isCaller) with h1 | h1
    · exact ⟨_, _, stEqOutX_prologueZ_le hW0 he.abi hx30
        (fun k h8 h16 => RL.lrWord_Zc hW0 _ _ h8 h16)
        (stEqOutX_entryZ hW0 he.abi he'.abi he.body he'.body (fun _ h => h) hsw hag hx29
          (c := .run ⟨0, [], fun _ => ρ₀ 0, w₀⟩) (c' := .run ⟨0, [], fun _ => ρ₀ 0, w₀'⟩)
          (fun _ h => h)).symm i (Nat.le_of_lt h1)⟩
    · rcases Nat.lt_or_ge i (prologueSteps af.saves af.frameSize af.isCaller + N) with h2 | h2
      · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueSteps af.saves af.frameSize af.isCaller) + j :=
          ⟨i - (prologueSteps af.saves af.frameSize af.isCaller), by omega⟩
        obtain ⟨c, c', hcc⟩ := hlk j (by omega)
        exact ⟨_, _, hcc.symm⟩
      · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueSteps af.saves af.frameSize af.isCaller) + N + j :=
          ⟨i - (prologueSteps af.saves af.frameSize af.isCaller + N), by omega⟩
        rw [hs, hs]
        exact ⟨_, _, hepi j (by rw [hRe] at hi; omega)⟩

end

end E2E
