import FV.E2E.BackendTwoRunNIU
import FV.E2E.BackendTwoRunNZWP
import FV.E2E.BackendTwoRunNV

/-!
# The two-run lock by induction on the call count, cleanup path (SEM1 #537, #713, #729)

`backend_twoRunLERWZNpWP`, `backend_twoRunLERWZIUP` (`BackendTwoRunNZWP.lean`,
`BackendTwoRunNIUP.lean`: `hcall` told the first run's segment start, both runs' facts at the
return) and `backend_twoRunLERWZNpW`, `backend_twoRunLERWZNp`, `backend_twoRunLERWZI`,
`backend_twoRunLERWZIU` (`BackendTwoRunNZW.lean`, `BackendTwoRunNZ.lean`, `BackendTwoRunNI.lean`,
`BackendTwoRunNIU.lean`) for the shipped compiler's cleanup path (`CompiledCleanup`), on
`backend_twoRunLWNpPV`: the given paired run is one of the guarded paired value semantics
`pairDI (valueSemV (GotV vcp) F ctx) F ctx XI`. Premises (but `hc` and the paired run) and
conclusions are those of the legacy theorems; same proofs (the forms without `SegFrom`/return
facts are corollaries).

* **`backend_twoRunLERWZNpWPV`**, `backend_twoRunLERWZNpWV`, `backend_twoRunLERWZNpV`;
* **`backend_twoRunLERWZIV`**, **`backend_twoRunLERWZIUPV`**, `backend_twoRunLERWZIUV`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 8000000 in
/-- **`backend_twoRunLERWZNpWP` on the cleanup path**: `hcall` also told the first run's segment
start (`RL.SegFrom`), both runs' facts at the return (#729). -/
theorem backend_twoRunLERWZNpWPV (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {XI : ExtSemI} {K : Nat} {F : BitVec 64 → Prop}
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    {us : List (Reg × Reg)} {outs : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {b kk : Nat} {ρ : Nat → CV} {w₁ : (Arm.ArmState × Arm.ArmState) × Nat} {vb : VBlock}
    {ops : Array Operand} {outs' : List CV}
    (hs : Star (VStep vcp
      (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI))
      (.run ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩) (.run ⟨b, kk, ρ, w₁⟩))
    (hvb : vcp.blocks[b]? = some vb) (hk : vb.insts[kk]? = some (.rets us))
    (hops : (MInst.rets us).operands = .ok ops) (hvals : outs = vuses ops ρ)
    (hsem : pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI
      (.rets us) outs w₁ = some (outs', w, .ret))
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
      ({ R with X := (XI.upTo N).at n } : RL).SegFrom (fun u =>
        OnCall ({ R with X := (XI.upTo N).at 0 } : RL).step R.fa R.base R.s0 n u ∧
          spOf u = R.spB) c i u →
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
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0)
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0).mem a =
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0).mem a) ∧
      Arm.read_mem_bytes 16 (spv s - 16#64) (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) = xreg 30 s ++ xreg 29 s ∧
      Arm.read_mem_bytes 16 (spv t0 - 16#64)
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = xreg 30 t0 ++ xreg 29 t0 ∧
      (∀ a, G a → (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0).mem a = s.mem a) ∧
      (∀ a, G' a → (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0).mem a = t0.mem a) ∧
      Arm.r .ERR (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = .None ∧
      spv (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = spv t0 ∧
      xreg 29 (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = xreg 29 t0 ∧
      (∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen,
        R.Good (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G' } : RL).Good
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)) ∧
      ∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)
          (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0)) ∧
    (N < w₁.2 → ∃ T,
      (∀ i ≤ (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)
          (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0)) ∧
      countIn (RL.CallSt R) ({ R with X := (XI.upTo N).at 0 } : RL).step R.s0
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) = N ∧
      countIn (RL.CallSt R) ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step t0
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) = N ∧
      R.CallSt (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) R.s0) ∧
      R.CallSt (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) t0) ∧
      ∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) t0).mem a =
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) R.s0).mem a) := by
  have hW0 : ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
      X := (XI.upTo N).at 0 } : RL).Wf := by
    obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hc.emit
    subst hk
    obtain ⟨ckc, ins, hck⟩ := checked_of_checkAlloc hc.check
    obtain ⟨a0, hat, hle⟩ := hck.at
    exact ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, hc.alloc, hc.emit, hc.layout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he.abi.fits; omega, he.stack,
      ⟨body, hpsF⟩, he.abi.program, he.gfree⟩
  have hW0' : ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
      s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).Wf := by
    obtain ⟨-, -, -, -, hk⟩ := emitFunc_ok hc.emit
    subst hk
    obtain ⟨ckc, ins, hck⟩ := checked_of_checkAlloc hc.check
    obtain ⟨a0, hat, hle⟩ := hck.at
    exact ⟨⟨ckc, ins, a0, hat, entryOk_of_le hle⟩, hc.alloc, hc.emit, hc.layout, hlm,
      by show 4 * fb.words.size ≤ 2 ^ 64; have := he'.abi.fits; omega, he'.stack,
      ⟨body, hpsF⟩, he'.abi.program, he'.gfree⟩
  have hPe : (prologueLines (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G
      (GotV vcp)).af.saves (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G
      (GotV vcp)).af.frameSize (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G
      (GotV vcp)).af.isCaller).length = (prologueLines af.saves af.frameSize af.isCaller).length := rfl
  -- the prologue part of the lock
  have hpro : ∀ i ≤ (prologueLines af.saves af.frameSize af.isCaller).length, ∃ d d', StEqOutX
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
  obtain ⟨hfull, hpre⟩ := backend_twoRunLWNpPV hc ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF he he'
    hR hcov hx30 hcall htls hag hx29
  refine ⟨fun hN => ?_, fun hN => ?_⟩
  · obtain ⟨T, e, e', hlk, ⟨⟨W, hqA, hqB⟩, -, -, hLB⟩, hpc, hpc', hre, hre', hgood⟩ :=
      hfull hN
    refine ⟨T, hpc, hpc', ?_⟩
    have hs : ∀ (g : Arm.ArmState → Arm.ArmState) (x : Arm.ArmState) (j : Nat),
        iterN g ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + j) x =
          iterN g j (iterN g ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) x) :=
      fun g x j => iterN_add ..
    subst hR
    have hr1 : ∃ ms, e = .run ms := by
      obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hre; exact ⟨_, rfl⟩
    have hr2 : ∃ ms, e' = .run ms := by
      obtain ⟨_, _, _, _, _, _, _, _, rfl, -⟩ := hre'; exact ⟨_, rfl⟩
    obtain ⟨hra, -, hm, hepi⟩ := RL.retLock_rets hW0 he.abi hx30
      (QWA.qaX hqA hW0 he.abi) hre hLB.1.symm
    obtain ⟨f1, g1, -, -, -⟩ := RL.retFacts_rets hW0 he.abi
      (QWA.qaX hqA hW0 he.abi) hre
    obtain ⟨f2, g2, e2, sp2, x2⟩ := RL.retFacts_rets hW0' he'.abi
      (QWA.qaX hqB hW0' he'.abi) hre'
    refine ⟨by rw [hs, hs]; exact hra, fun a hFa hDa => ?_, by rw [hs]; exact f1,
      by rw [hs]; exact f2, fun a ha => by rw [hs]; exact g1 a ha,
      fun a ha => by rw [hs]; exact g2 a ha, by rw [hs]; exact e2, by rw [hs]; exact sp2,
      by rw [hs]; exact x2, hgood, fun i hi => ?_⟩
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
      rcases Nat.lt_or_ge i (prologueLines af.saves af.frameSize af.isCaller).length with h1 | h1
      · exact hpro i (Nat.le_of_lt h1)
      · rcases Nat.lt_or_ge i ((prologueLines af.saves af.frameSize af.isCaller).length + T) with h2 | h2
        · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueLines af.saves af.frameSize af.isCaller).length + j :=
            ⟨i - (prologueLines af.saves af.frameSize af.isCaller).length, by omega⟩
          obtain ⟨c, c', hcc⟩ := hlk j (by omega)
          exact ⟨_, _, hcc.symm⟩
        · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueLines af.saves af.frameSize af.isCaller).length + T + j :=
            ⟨i - ((prologueLines af.saves af.frameSize af.isCaller).length + T), by omega⟩
          rw [hs, hs]
          exact ⟨_, _, hepi j (by rw [hRe] at hi; omega)⟩
  · obtain ⟨T, b, k, a, its, m, w, a', its', m', w', hlk, ⟨⟨W, hqA, -⟩, -, -, hLB⟩, hc1, hc2,
      vb, i, hvb, hi, hcI⟩ := hpre hN
    subst hR
    have hcs : (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp)).CallSt
        (iterN ({ actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp) with
          X := (XI.upTo N).at 0 } : RL).step ((prologueLines af.saves af.frameSize af.isCaller).length + T) s) :=
      RL.callSt_of_q_call (qa_q (QWA.qaX hqA hW0 he.abi)).choose_spec hvb hi hcI
    have hpcEq := hLB.1.1 .PC (by simp)
    refine ⟨T, fun i hi => ?_, hc1, hc2, hcs, ?_, fun x hFx hDx => ?_⟩
    · rw [hPe] at hi
      rcases Nat.lt_or_ge i (prologueLines af.saves af.frameSize af.isCaller).length with h1 | h1
      · exact hpro i (Nat.le_of_lt h1)
      · obtain ⟨j, rfl⟩ : ∃ j, i = (prologueLines af.saves af.frameSize af.isCaller).length + j :=
          ⟨i - (prologueLines af.saves af.frameSize af.isCaller).length, by omega⟩
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

set_option maxHeartbeats 8000000 in
/-- **`backend_twoRunLERWZNpW` on the cleanup path** (`backend_twoRunLERWZNpWPV` with `hcall` in
`backend_twoRunLERWZNpW`'s shape, without the return facts). -/
theorem backend_twoRunLERWZNpWV (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {XI : ExtSemI} {K : Nat} {F : BitVec 64 → Prop}
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    {us : List (Reg × Reg)} {outs : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {b kk : Nat} {ρ : Nat → CV} {w₁ : (Arm.ArmState × Arm.ArmState) × Nat} {vb : VBlock}
    {ops : Array Operand} {outs' : List CV}
    (hs : Star (VStep vcp
      (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI))
      (.run ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩) (.run ⟨b, kk, ρ, w₁⟩))
    (hvb : vcp.blocks[b]? = some vb) (hk : vb.insts[kk]? = some (.rets us))
    (hops : (MInst.rets us).operands = .ok ops) (hvals : outs = vuses ops ρ)
    (hsem : pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI
      (.rets us) outs w₁ = some (outs', w, .ret))
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
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0)
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0).mem a =
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0).mem a) ∧
      ∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)
          (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0)) ∧
    (N < w₁.2 → ∃ T,
      (∀ i ≤ (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)
          (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0)) ∧
      countIn (RL.CallSt R) ({ R with X := (XI.upTo N).at 0 } : RL).step R.s0
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) = N ∧
      countIn (RL.CallSt R) ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step t0
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) = N ∧
      R.CallSt (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) R.s0) ∧
      R.CallSt (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) t0) ∧
      ∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) t0).mem a =
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) R.s0).mem a) := by
  obtain ⟨h1, h2⟩ := backend_twoRunLERWZNpWPV hc ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF he he'
    hR hcov hx30 (fun n n' c c' i u u' hin _ hin' => hcall n n' c c' i u u' hin hin') htls hag hx29
  refine ⟨fun hN => ?_, h2⟩
  obtain ⟨T, a1, a2, a3, a4, -, -, -, -, -, -, -, -, a5⟩ := h1 hN
  exact ⟨T, a1, a2, a3, a4, a5⟩

set_option maxHeartbeats 8000000 in
/-- **`backend_twoRunLERWZNp` on the cleanup path** (`backend_twoRunLERWZNpWV` without the
memory conjunct of the prefix case). -/
theorem backend_twoRunLERWZNpV (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {XI : ExtSemI} {K : Nat} {F : BitVec 64 → Prop}
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    {us : List (Reg × Reg)} {outs : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {b kk : Nat} {ρ : Nat → CV} {w₁ : (Arm.ArmState × Arm.ArmState) × Nat} {vb : VBlock}
    {ops : Array Operand} {outs' : List CV}
    (hs : Star (VStep vcp
      (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI))
      (.run ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩) (.run ⟨b, kk, ρ, w₁⟩))
    (hvb : vcp.blocks[b]? = some vb) (hk : vb.insts[kk]? = some (.rets us))
    (hops : (MInst.rets us).operands = .ok ops) (hvals : outs = vuses ops ρ)
    (hsem : pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI
      (.rets us) outs w₁ = some (outs', w, .ret))
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
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0)
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0).mem a =
        (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0).mem a) ∧
      ∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)
          (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0)) ∧
    (N < w₁.2 → ∃ T,
      (∀ i ≤ (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step i t0)
          (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step i R.s0)) ∧
      countIn (RL.CallSt R) ({ R with X := (XI.upTo N).at 0 } : RL).step R.s0
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) = N ∧
      countIn (RL.CallSt R) ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step t0
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) = N ∧
      R.CallSt (iterN ({ R with X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) R.s0) ∧
      R.CallSt (iterN ({ R with s0 := t0, G := G', X := (XI.upTo N).at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T) t0)) := by
  obtain ⟨h1, h2⟩ := backend_twoRunLERWZNpWV hc ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF he he' hR
    hcov hx30 hcall htls hag hx29
  refine ⟨h1, fun hN => ?_⟩
  obtain ⟨T, a, b, c, d, e, -⟩ := h2 hN
  exact ⟨T, a, b, c, d, e⟩

set_option maxHeartbeats 8000000 in
/-- **`backend_twoRunLERWZI` on the cleanup path** (same proof, on `backend_twoRunLERWZNpV`). -/
theorem backend_twoRunLERWZIV (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {XI : ExtSemI} {K : Nat} {F : BitVec 64 → Prop}
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    {us : List (Reg × Reg)} {outs : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {b kk : Nat} {ρ : Nat → CV} {w₁ : (Arm.ArmState × Arm.ArmState) × Nat} {vb : VBlock}
    {ops : Array Operand} {outs' : List CV}
    (hs : Star (VStep vcp
      (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI))
      (.run ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩) (.run ⟨b, kk, ρ, w₁⟩))
    (hvb : vcp.blocks[b]? = some vb) (hk : vb.insts[kk]? = some (.rets us))
    (hops : (MInst.rets us).operands = .ok ops) (hvals : outs = vuses ops ρ)
    (hsem : pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI
      (.rets us) outs w₁ = some (outs', w, .ret))
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {H : ArmHooks} {G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀)
    (he0 : ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' 0)
    (hC' : ∀ n, CalleeOkGP (fun u => (OnCallPR Kp' cc' P' Rr' (ArmStepX (XI.at 0) H fa) fa base t0 n u ∧
        spOf u = spv t0 - BitVec.ofNat 64 (frameDrop af)) ∧
        (CallPc fa base (Arm.r .PC u) → LockedAt (ArmStepX (XI.at 0) H fa) fa base K
          (spv s - BitVec.ofNat 64 (frameDrop af)) s t0 n u))
      F K G' t0 (CallAt fa base) (XI.at n) H vcp.CallSite (GotV vcp))
    (hT' : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
        (OnCallPR Kp' cc' P' Rr' (ArmStepX (XI.at 0) H fa) fa base t0 n u ∧
          spOf u = spv t0 - BitVec.ofNat 64 (frameDrop af)) ∧
        (CallPc fa base (Arm.r .PC u) → LockedAt (ArmStepX (XI.at 0) H fa) fa base K
          (spv s - BitVec.ofNat 64 (frameDrop af)) s t0 n u))
      F K G' t0 (CallAt fa base) (XI.at n) H vcp.TrySite (GotV vcp))
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc)
    (hx30 : fa.x30Free lm = true)
    (hcall : ∀ N n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      ∀ x d, ({ R with X := (XI.upTo N).at n } : RL).AtLine u x → LineDest x d →
      StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ N n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      (∃ a b c, ({ R with X := (XI.upTo N).at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hag : EntryAgree (frameDrop af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∃ T,
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0)
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0).mem a =
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0).mem a) ∧
      ∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) := by
  subst hR
  -- the core theorem at `N`
  have core := fun (N : Nat)
      (heN : ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' N) =>
    backend_twoRunLERWZNpV (R := actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp))
      hc ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF (he.toN N) heN rfl hcov hx30 (hcall N)
      (htls N) hag hx29
  -- induction on the call count
  have hind : ∀ N, N ≤ w₁.2 →
      ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' N := by
    intro N
    induction N with
    | zero => exact fun _ => he0
    | succ N ih =>
      intro hN
      have heN := ih (by omega)
      obtain ⟨T, hlk, -, hc2, -, hcs2⟩ := (core N heN).2 (by omega)
      have hcb : callsBefore (ArmStepX (XI.at 0) H fa) fa base t0
          ((prologueLines af.saves af.frameSize af.isCaller).length + T) = N := by
        rw [callsBefore_eq_countIn]; exact hc2
      have hcs : CallPc fa base (Arm.r .PC (runX (ArmStepX (XI.at 0) H fa)
          ((prologueLines af.saves af.frameSize af.isCaller).length + T) t0)) := by
        rw [runX_eq]; exact hcs2
      have hlockN : ∀ u, CallPc fa base (Arm.r .PC u) →
          OnCall (ArmStepX (XI.at 0) H fa) fa base t0 N u →
          LockedAt (ArmStepX (XI.at 0) H fa) fa base K
            (spv s - BitVec.ofNat 64 (frameDrop af)) s t0 N u := by
        intro u hpc ⟨i, hu, hi⟩
        have hle := callsBefore_le_of_callSt hcb hcs hi
        obtain ⟨d, d', hz⟩ := hlk i hle
        refine ⟨i, (actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp)).Zc d d', hu,
          hi, ?_, fun a ha hzz => hzz.2.2.1 ha⟩
        rw [← hu, runX_eq, runX_eq]
        exact hz
      refine ⟨heN.abi, heN.stack, heN.gfree, heN.hF, heN.proph, heN.regp, fun n hn => ?_,
        fun ht n hn => ?_, heN.pc, heN.tls, heN.body⟩
      · rcases Nat.lt_or_ge n N with h | h
        · exact heN.calls n h
        · obtain rfl : n = N := by omega
          exact (hC' n).mono fun u hu =>
            ⟨hu, fun hpc => hlockN u hpc hu.1.1.1⟩
      · rcases Nat.lt_or_ge n N with h | h
        · exact heN.tries ht n h
        · obtain rfl : n = N := by omega
          exact (hT' ht n).mono fun u hu =>
            ⟨hu, fun hpc => hlockN u hpc hu.1.1.1⟩
  exact (core w₁.2 (hind w₁.2 (Nat.le_refl _))).1 (Nat.le_refl _)

set_option maxHeartbeats 8000000 in
/-- **`backend_twoRunLERWZIUP` on the cleanup path** (same proof, on `backend_twoRunLERWZNpWPV`):
the second activation's contracts only at its call states `LockedUpTo` the first run, `hcall` also
told the first run's segment start (`RL.SegFrom`), both runs' facts at the return (#729). -/
theorem backend_twoRunLERWZIUPV (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {XI : ExtSemI} {K : Nat} {F : BitVec 64 → Prop}
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    {us : List (Reg × Reg)} {outs : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {b kk : Nat} {ρ : Nat → CV} {w₁ : (Arm.ArmState × Arm.ArmState) × Nat} {vb : VBlock}
    {ops : Array Operand} {outs' : List CV}
    (hs : Star (VStep vcp
      (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI))
      (.run ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩) (.run ⟨b, kk, ρ, w₁⟩))
    (hvb : vcp.blocks[b]? = some vb) (hk : vb.insts[kk]? = some (.rets us))
    (hops : (MInst.rets us).operands = .ok ops) (hvals : outs = vuses ops ρ)
    (hsem : pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI
      (.rets us) outs w₁ = some (outs', w, .ret))
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {H : ArmHooks} {G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀)
    (he0 : ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' 0)
    (hC' : ∀ n, CalleeOkGP (fun u => (OnCallPR Kp' cc' P' Rr' (ArmStepX (XI.at 0) H fa) fa base t0 n u ∧
        spOf u = spv t0 - BitVec.ofNat 64 (frameDrop af)) ∧
        (CallPc fa base (Arm.r .PC u) → LockedUpTo (ArmStepX (XI.at 0) H fa) fa base K
          (spv s - BitVec.ofNat 64 (frameDrop af)) F D s t0 n u))
      F K G' t0 (CallAt fa base) (XI.at n) H vcp.CallSite (GotV vcp))
    (hT' : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
        (OnCallPR Kp' cc' P' Rr' (ArmStepX (XI.at 0) H fa) fa base t0 n u ∧
          spOf u = spv t0 - BitVec.ofNat 64 (frameDrop af)) ∧
        (CallPc fa base (Arm.r .PC u) → LockedUpTo (ArmStepX (XI.at 0) H fa) fa base K
          (spv s - BitVec.ofNat 64 (frameDrop af)) F D s t0 n u))
      F K G' t0 (CallAt fa base) (XI.at n) H vcp.TrySite (GotV vcp))
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc)
    (hx30 : fa.x30Free lm = true)
    (hcall : ∀ N n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with X := (XI.upTo N).at n } : RL).SegFrom (fun u =>
        OnCall ({ R with X := (XI.upTo N).at 0 } : RL).step R.fa R.base R.s0 n u ∧
          spOf u = R.spB) c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      ∀ x d, ({ R with X := (XI.upTo N).at n } : RL).AtLine u x → LineDest x d →
      StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ N n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      (∃ a b c, ({ R with X := (XI.upTo N).at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hag : EntryAgree (frameDrop af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∃ T,
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0)
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0).mem a =
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0).mem a) ∧
      Arm.read_mem_bytes 16 (spv s - 16#64) (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) = xreg 30 s ++ xreg 29 s ∧
      Arm.read_mem_bytes 16 (spv t0 - 16#64)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = xreg 30 t0 ++ xreg 29 t0 ∧
      (∀ a, G a → (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0).mem a = s.mem a) ∧
      (∀ a, G' a → (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0).mem a = t0.mem a) ∧
      Arm.r .ERR (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = .None ∧
      spv (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = spv t0 ∧
      xreg 29 (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = xreg 29 t0 ∧
      (∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen,
        R.Good (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G' } : RL).Good
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)) ∧
      ∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) := by
  subst hR
  -- the core theorem at `N`
  have core := fun (N : Nat)
      (heN : ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' N) =>
    backend_twoRunLERWZNpWPV (R := actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp))
      hc ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF (he.toN N) heN rfl hcov hx30 (hcall N)
      (htls N) hag hx29
  -- induction on the call count
  have hind : ∀ N, N ≤ w₁.2 →
      ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' N := by
    intro N
    induction N with
    | zero => exact fun _ => he0
    | succ N ih =>
      intro hN
      have heN := ih (by omega)
      obtain ⟨T, hlk, -, hc2, -, hcs2, hmemN⟩ := (core N heN).2 (by omega)
      have hcb : callsBefore (ArmStepX (XI.at 0) H fa) fa base t0
          ((prologueLines af.saves af.frameSize af.isCaller).length + T) = N := by
        rw [callsBefore_eq_countIn]; exact hc2
      have hcs : CallPc fa base (Arm.r .PC (runX (ArmStepX (XI.at 0) H fa)
          ((prologueLines af.saves af.frameSize af.isCaller).length + T) t0)) := by
        rw [runX_eq]; exact hcs2
      have hlockN : ∀ u, CallPc fa base (Arm.r .PC u) →
          OnCall (ArmStepX (XI.at 0) H fa) fa base t0 N u →
          LockedUpTo (ArmStepX (XI.at 0) H fa) fa base K
            (spv s - BitVec.ofNat 64 (frameDrop af)) F D s t0 N u := by
        intro u hpc ⟨i, hu, hi⟩
        have hle := callsBefore_le_of_callSt hcb hcs hi
        have hpci : CallPc fa base (Arm.r .PC (runX (ArmStepX (XI.at 0) H fa) i t0)) := by
          rw [hu]; exact hpc
        have hge := callsBefore_le_of_callSt hi hpci hcb
        obtain rfl : i = (prologueLines af.saves af.frameSize af.isCaller).length + T := by omega
        refine ⟨_, hu, hi, fun j hj => ?_, fun a hFa hDa => ?_⟩
        · obtain ⟨d, d', hz⟩ := hlk j (Nat.le_trans hj hle)
          refine ⟨(actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp)).Zc d d', ?_,
            fun a ha hzz => hzz.2.2.1 ha⟩
          rw [runX_eq, runX_eq]
          exact hz
        · rw [← hu, runX_eq, runX_eq]
          exact hmemN a hFa hDa
      refine ⟨heN.abi, heN.stack, heN.gfree, heN.hF, heN.proph, heN.regp, fun n hn => ?_,
        fun ht n hn => ?_, heN.pc, heN.tls, heN.body⟩
      · rcases Nat.lt_or_ge n N with h | h
        · exact heN.calls n h
        · obtain rfl : n = N := by omega
          exact (hC' n).mono fun u hu =>
            ⟨hu, fun hpc => hlockN u hpc hu.1.1.1⟩
      · rcases Nat.lt_or_ge n N with h | h
        · exact heN.tries ht n h
        · obtain rfl : n = N := by omega
          exact (hT' ht n).mono fun u hu =>
            ⟨hu, fun hpc => hlockN u hpc hu.1.1.1⟩
  exact (core w₁.2 (hind w₁.2 (Nat.le_refl _))).1 (Nat.le_refl _)

set_option maxHeartbeats 8000000 in
/-- **`backend_twoRunLERWZIU` on the cleanup path** (`backend_twoRunLERWZIUPV` with `hcall` in
`backend_twoRunLERWZIU`'s shape, without the return facts). -/
theorem backend_twoRunLERWZIUV (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {XI : ExtSemI} {K : Nat} {F : BitVec 64 → Prop}
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (ρ₀ : Nat → CV)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    {us : List (Reg × Reg)} {outs : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {b kk : Nat} {ρ : Nat → CV} {w₁ : (Arm.ArmState × Arm.ArmState) × Nat} {vb : VBlock}
    {ops : Array Operand} {outs' : List CV}
    (hs : Star (VStep vcp
      (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI))
      (.run ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩) (.run ⟨b, kk, ρ, w₁⟩))
    (hvb : vcp.blocks[b]? = some vb) (hk : vb.insts[kk]? = some (.rets us))
    (hops : (MInst.rets us).operands = .ok ops) (hvals : outs = vuses ops ρ)
    (hsem : pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI
      (.rets us) outs w₁ = some (outs', w, .ret))
    {lm : Std.HashMap Lbl Nat} (hlm : labelOffsets fa.lines = .ok lm) {body : List Line}
    {psF : PState} (hpsF : blocksLinesE ⟨fa.k, af.slotBase⟩ af af.blocks.toList {} = .ok (body, psF))
    {H : ArmHooks} {G G' : BitVec 64 → Prop}
    {base ra ra' : BitVec 64} {Kp Kp' : Nat} {cc cc' : BitVec 64} {P P' : Nat → BitVec 64 → BitVec 8}
    {Rr Rr' : Nat → Arm.ArmState} {s t0 : Arm.ArmState}
    (he : ActEntryPR vcp rf af fa fb K F G XI H base ra Kp cc P Rr s w₀)
    (he0 : ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' 0)
    (hC' : ∀ n, CalleeOkGP (fun u => (OnCallPR Kp' cc' P' Rr' (ArmStepX (XI.at 0) H fa) fa base t0 n u ∧
        spOf u = spv t0 - BitVec.ofNat 64 (frameDrop af)) ∧
        (CallPc fa base (Arm.r .PC u) → LockedUpTo (ArmStepX (XI.at 0) H fa) fa base K
          (spv s - BitVec.ofNat 64 (frameDrop af)) F D s t0 n u))
      F K G' t0 (CallAt fa base) (XI.at n) H vcp.CallSite (GotV vcp))
    (hT' : vcp.hasTryCall = true → ∀ n, CalleeTryOkGP (fun u =>
        (OnCallPR Kp' cc' P' Rr' (ArmStepX (XI.at 0) H fa) fa base t0 n u ∧
          spOf u = spv t0 - BitVec.ofNat 64 (frameDrop af)) ∧
        (CallPc fa base (Arm.r .PC u) → LockedUpTo (ArmStepX (XI.at 0) H fa) fa base K
          (spv s - BitVec.ofNat 64 (frameDrop af)) F D s t0 n u))
      F K G' t0 (CallAt fa base) (XI.at n) H vcp.TrySite (GotV vcp))
    {R : RL} (hR : R = actRL vcp rf af fa fb lm base s XI H psF K G (GotV vcp))
    (hcov : FormsCovered R.ctx R.vc)
    (hx30 : fa.x30Free lm = true)
    (hcall : ∀ N n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      ∀ x d, ({ R with X := (XI.upTo N).at n } : RL).AtLine u x → LineDest x d →
      StEqOutX (R.Zc c c') (H.call d u) (H.call d u'))
    (htls : ∀ N n n' c c' i u u', ({ R with X := (XI.upTo N).at n } : RL).InSeg (OkDiff F c c') c i u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).InSeg (OkDiff F c c') c' i u' →
      ({ R with X := (XI.upTo N).at n } : RL).GoodX u →
      ({ R with s0 := t0, G := G', X := (XI.upTo N).at n' } : RL).GoodX u' →
      StEqOutX (R.Zc c c') u u' → (∀ a, MConf.WDiff c c' a → F a ∨ D a) →
      (∃ a b c, ({ R with X := (XI.upTo N).at n } : RL).AtLine u (.ldrTlsDescLo12 a b c)) →
      ∀ m r, StEqOutX (R.Zc c c') (H.tls m r u) (H.tls m r u'))
    (hag : EntryAgree (frameDrop af + K) s t0)
    (hx29 : Arm.r (.GPR 29#5) s = Arm.r (.GPR 29#5) t0) :
    ∃ T,
      Arm.r .PC (iterN ({ R with X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0)
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) t0).mem a =
        (iterN ({ R with X := XI.at 0 } : RL).step
          ((prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen) R.s0).mem a) ∧
      ∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) := by
  obtain ⟨T, a1, a2, a3, a4, -, -, -, -, -, -, -, -, a5⟩ := backend_twoRunLERWZIUPV hc ρ₀ hsw hs hvb
    hk hops hvals hsem hlm hpsF he he0 hC' hT' hR hcov hx30
    (fun N n n' c c' i u u' hin _ hin' => hcall N n n' c c' i u u' hin hin') htls hag hx29
  exact ⟨T, a1, a2, a3, a4, a5⟩

end

end E2E
