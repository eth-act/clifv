import FV.E2E.BackendTwoRunNIU
import FV.E2E.BackendTwoRunNZWPK

/-!
# The two-run lock with the lock set inside `F ∪ D` and `RL.GoodK` of both runs (SEM1 #537, #713)

**`backend_twoRunLERWZIUPK`**: `backend_twoRunLERWZIUP` whose per-index lock is on
`R.Zc d d' ∩ (F ∪ D)` and with `RL.GoodK` of both runs at every index before the return (same
proof, on `backend_twoRunLERWZNpWPK`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 8000000 in
/-- **`backend_twoRunLERWZIUP` with the lock set inside `F ∪ D` and `RL.GoodK` of both runs**
(module doc). -/
theorem backend_twoRunLERWZIUPK (hc : Compiled f k vc vcp rf af fa fb)
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
      Arm.read_mem_bytes 16 (spv t0 - 16#64) (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
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
        R.GoodK (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) ∧
        ({ R with s0 := t0, G := G' } : RL).GoodK
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)) ∧
      ∀ i < (prologueLines R.af.saves R.af.frameSize R.af.isCaller).length + T + R.retLen, ∃ d d',
        StEqOutX (fun a => R.Zc d d' a ∧ (F a ∨ D a))
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) := by
  subst hR
  -- the core theorem at `N`
  have core := fun (N : Nat)
      (heN : ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' N) =>
    backend_twoRunLERWZNpWPK (R := actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp))
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

end

end E2E
