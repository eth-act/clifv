import FV.E2E.BackendTwoRunN
import FV.E2E.RegLevelCallStart

/-!
# The per-index lock with the contracts of the first `N` calls, the world agreement at the call
state (SEM1 #537, #713)

`backend_twoRunLERWZNp`'s prefix case gives the lock `StEqOutX (R.Zc d d')` at the `N`-th call
states, whose set contains the bytes where the two VCode worlds differ (`WDiff`); it forgets that
those are in `F ∪ D` (the joint invariant's `WIn`). At the link the second run's call contract is
the first run's stage 2, which reads the world outside `F`, so it needs the two call states'
memories equal outside `F ∪ D`. **`backend_twoRunLERWZNpW`**: `backend_twoRunLERWZNp` with that
conjunct in the prefix case (same proof; the invariant is at hand there).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 8000000 in
/-- **`backend_twoRunLERWZNp` with the memories of the `N`-th call states equal outside
`F ∪ D`** (module doc). -/
theorem backend_twoRunLERWZNpW (hc : Compiled f k vc vcp rf af fa fb)
    {XI : ExtSemI} {K : Nat} {F : BitVec 64 → Prop}
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    {us : List (Reg × Reg)} {outs : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {b kk : Nat} {ρ : Nat → CV} {w₁ : (Arm.ArmState × Arm.ArmState) × Nat} {vb : VBlock}
    {ops : Array Operand} {outs' : List CV}
    (hs : Star (VStep vcp
      (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI))
      (.run ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩) (.run ⟨b, kk, ρ, w₁⟩))
    (hvb : vcp.blocks[b]? = some vb) (hk : vb.insts[kk]? = some (.rets us))
    (hops : (MInst.rets us).operands = .ok ops) (hvals : outs = vuses ops ρ)
    (hsem : pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI (.rets us)
      outs w₁ = some (outs', w, .ret))
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {H : ArmHooks} {G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState} {N : Nat}
    (he : ActEntryPRN vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀ N)
    (he' : ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' N)
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc)
    (hx30 : fa.x30Free lm = true)
    (hcall : ∀ n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      ∀ x d, ({ R with X := (XI.upTo N).at n } : RL).AtLine u x → LineDest x d →
      StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      (∃ a b c, ({ R with X := (XI.upTo N).at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hag : EntryAgree (frameDrop af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    (w₁.2 ≤ N → ∃ T,
      Arm.r .PC (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) t0)
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) t0).mem a =
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) R.s0).mem a) ∧
      ∀ i < (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) + T + R.retLen, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)
          (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0)) ∧
    (N < w₁.2 → ∃ T,
      (∀ i ≤ (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) + T, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)
          (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0)) ∧
      countIn (RL.CallSt R) ({ R with X := (XI.upTo N).at 0 } : RL).step R.s0
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T) = N ∧
      countIn (RL.CallSt R) ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step t0
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T) = N ∧
      R.CallSt (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T) R.s0) ∧
      R.CallSt (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T) t0) ∧
      ∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T) t0).mem a =
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T) R.s0).mem a) := by
  have hW0 : ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
      X := (XI.upTo N).at 0 } : RL).Wf := by
    obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hc.emit
    subst hk
    obtain ⟨ckc, ins, hck⟩ := checked_of_checkAlloc hc.check
    obtain ⟨a0, hat, hle⟩ := hck.at
    exact ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, hc.alloc, hc.emit, hc.layout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack,
      ⟨body, hpsF⟩, he.abi.program, he.gfree⟩
  have hPe : (prologueLines (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G
      (GotV vcp)).af.saves (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G
      (GotV vcp)).af.frameSize (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G
      (GotV vcp)).af.isCaller).length = (prologueSteps af.saves af.frameSize af.isCaller) := rfl
  -- the prologue part of the lock
  have hpro : ∀ i ≤ (prologueSteps af.saves af.frameSize af.isCaller), ∃ d d', StEqOutX
      ((actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp)).Zc d d')
      (iterN ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
        s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)
      (iterN ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
        X := (XI.upTo N).at 0 } : RL).step i s) := fun i hi => by
    have hF := he.hF
    subst hF
    exact ⟨_, _, stEqOutX_prologueZ_le hW0 he.abi hx30
      (fun k h8 h16 => RL.lrWord_Zc hW0 _ _ h8 h16)
      (stEqOutX_entryZ hW0 he.abi he'.abi he.body he'.body (fun _ h => h) hsw hag hx29
        (c := .run ⟨0, [], fun _ => ρ₀ 0, w₀⟩) (c' := .run ⟨0, [], fun _ => ρ₀ 0, w₀'⟩)
        (fun _ h => h)).symm i hi⟩
  obtain ⟨hfull, hpre⟩ := backend_twoRunLWNp hc ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF he he'
    hR hcov hx30 hcall htls hag hx29
  refine ⟨fun hN => ?_, fun hN => ?_⟩
  · obtain ⟨T, e, e', hlk, ⟨⟨W, hqA, -⟩, -, -, hLB⟩, hpc, hpc', hre, hre'⟩ := hfull hN
    refine ⟨T, hpc, hpc', ?_⟩
    have hs : ∀ (g : Arm.ArmState → Arm.ArmState) (x : Arm.ArmState) (j : Nat),
        iterN g (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + j) x =
          iterN g j (iterN g (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T) x) :=
      fun g x j => iterN_add ..
    subst hR
    have hr1 : ∃ ms, e = .run ms := by
      obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hre; exact ⟨_, rfl⟩
    have hr2 : ∃ ms, e' = .run ms := by
      obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hre'; exact ⟨_, rfl⟩
    obtain ⟨hra, -, hm, hepi⟩ := RL.retLock_rets hW0 he.abi hx30
      (QWA.qaX hqA hW0 he.abi) hre hLB.1.symm
    refine ⟨by rw [hs, hs]; exact hra, fun a hFa hDa => ?_, fun i hi => ?_⟩
    · rw [hs, hs]
      refine hm a ?_
      rintro ⟨-, -, -, hz⟩
      rcases hz with h | h
      · exact hFa (he.hF ▸ h)
      · rcases wDiff_of_wIn hr1 hr2 hLB.2.1 a h with h' | h'
        · exact hFa h'
        · exact hDa h'
    · have hRe : (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp)).retLen =
          ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
            X := (XI.upTo N).at 0 } : RL).retLen := rfl
      rw [hPe] at hi hs
      rcases Nat.lt_or_ge i (prologueSteps af.saves af.frameSize af.isCaller) with h1 | h1
      · exact hpro i (Nat.le_of_lt h1)
      · rcases Nat.lt_or_ge i (prologueSteps af.saves af.frameSize af.isCaller + T) with h2 | h2
        · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueSteps af.saves af.frameSize af.isCaller) + j :=
            ⟨i - (prologueSteps af.saves af.frameSize af.isCaller), by omega⟩
          obtain ⟨c, c', hcc⟩ := hlk j (by omega)
          exact ⟨_, _, hcc.symm⟩
        · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueSteps af.saves af.frameSize af.isCaller) + T + j :=
            ⟨i - (prologueSteps af.saves af.frameSize af.isCaller + T), by omega⟩
          rw [hs, hs]
          exact ⟨_, _, hepi j (by rw [hRe] at hi; omega)⟩
  · obtain ⟨T, b, k, a, its, m, w, a', its', m', w', hlk, ⟨⟨W, hqA, -⟩, -, -, hLB⟩, hc1, hc2,
      vb, i, hvb, hi, hcI⟩ := hpre hN
    subst hR
    have hcs : (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp)).CallSt
        (iterN ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
          X := (XI.upTo N).at 0 } : RL).step (prologueSteps af.saves af.frameSize af.isCaller + T) s) :=
      RL.callSt_of_q_call (qa_q (QWA.qaX hqA hW0 he.abi)).choose_spec hvb hi hcI
    have hpcEq := hLB.1.1 .PC (by simp)
    refine ⟨T, fun i hi => ?_, hc1, hc2, hcs, ?_, fun x hFx hDx => ?_⟩
    · rw [hPe] at hi
      rcases Nat.lt_or_ge i (prologueSteps af.saves af.frameSize af.isCaller) with h1 | h1
      · exact hpro i (Nat.le_of_lt h1)
      · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueSteps af.saves af.frameSize af.isCaller) + j :=
          ⟨i - (prologueSteps af.saves af.frameSize af.isCaller), by omega⟩
        rcases Nat.lt_or_ge j T with h2 | h2
        · obtain ⟨c, c', hcc⟩ := hlk j h2
          exact ⟨_, _, hcc.symm⟩
        · obtain rfl : j = T := by omega
          exact ⟨_, _, hLB.1.symm⟩
    · show CallPc _ _ _
      rw [← hpcEq]
      exact hcs
    · -- the world agreement at the call states (the joint invariant's `WIn`)
      refine (hLB.1.2.2 x ?_).symm
      rintro ⟨-, -, -, hz⟩
      rcases hz with h | h
      · exact hFx (he.hF ▸ h)
      · rcases wDiff_of_wIn ⟨_, rfl⟩ ⟨_, rfl⟩ hLB.2.1 x h with h' | h'
        · exact hFx h'
        · exact hDx h'

end

end E2E
