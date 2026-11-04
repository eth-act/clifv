import FV.E2E.BackendTwoRunNZ

/-!
# The two-run lock by induction on the call count (SEM1 #537, #713)

The first activation `s` meets every callee contract of `XI` (`ActEntryPR`); the second, `t0`,
meets the contract of call `n` only at its call-`n` states that are locked with the first run's
state of the same index (`LockedAt`): that is what the link can give it (`XI` answers from the
first run's prophecies; a state locked with the first run's call-`n` state has them). Along one
paired run of `XI` with `C` calls (`backend_pairRunD`'s output), induction on `N ≤ C`:
`ActEntryPRN … N` for `t0` gives, by `backend_twoRunLERWZNp`, the lock up to the call-`N` states,
so `t0`'s call-`N` states are locked and `ActEntryPRN … (N + 1)` holds; at `N = C` the lock holds
to the return.

* `LockedAt`, `callsBefore_le_of_callSt`;
* **`backend_twoRunLERWZI`**: `backend_twoRunLERWZ`'s conclusion for such a pair of entries.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **`u` is the second run's state at index `i`, `n` calls before it, locked with the first run's
state at `i`** by a set avoiding the `K` bytes below `c` (the callees' dead stack). -/
def LockedAt (Mm : Arm.ArmState → Arm.ArmState) (fa : FnAsm) (base : BitVec 64) (K : Nat)
    (c : BitVec 64) (s t : Arm.ArmState) (n : Nat) (u : Arm.ArmState) : Prop :=
  ∃ i Z, runX Mm i t = u ∧ callsBefore Mm fa base t i = n ∧ StEqOutX Z u (runX Mm i s) ∧
    ∀ a, StackBelow K c a → ¬ Z a

/-- **A call state with `N` calls before it bounds the states with `N` calls before them.** -/
theorem callsBefore_le_of_callSt {Mm : Arm.ArmState → Arm.ArmState} {fa : FnAsm}
    {base : BitVec 64} {t : Arm.ArmState} {j i N : Nat} (hj : callsBefore Mm fa base t j = N)
    (hc : CallPc fa base (Arm.r .PC (runX Mm j t))) (hi : callsBefore Mm fa base t i = N) :
    i ≤ j := by
  rcases Nat.lt_or_ge j i with h | h
  · exfalso
    have h1 := callsBefore_mono Mm fa base t (show j + 1 ≤ i by omega)
    have h2 : callsBefore Mm fa base t (j + 1) = callsBefore Mm fa base t j + 1 := by
      simp [callsBefore, hc]
    omega
  · exact h

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

set_option maxHeartbeats 8000000 in
/-- **The lock of two activations, the second meeting the contracts at its locked call states**
(module doc). -/
theorem backend_twoRunLERWZI (hc : Compiled f k vc vcp rf af fa fb)
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
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) R.s0) = ra ∧
      Arm.r .PC (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
        (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) t0) = ra' ∧
      RetAgreeX (frameDrop af + K) (spv s)
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) t0)
        (iterN ({ R with X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) R.s0) ∧
      (∀ a, ¬ F a → ¬ D a →
        (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) t0).mem a =
        (iterN ({ R with X := XI.at 0 } : RL).step
          (prologueSteps R.af.saves R.af.frameSize R.af.isCaller + T + R.retLen) R.s0).mem a) ∧
      ∀ i < (prologueSteps R.af.saves R.af.frameSize R.af.isCaller) + T + R.retLen, ∃ d d',
        StEqOutX (R.Zc d d')
          (iterN ({ R with s0 := t0, G := G', X := XI.at 0 } : RL).step i t0)
          (iterN ({ R with X := XI.at 0 } : RL).step i R.s0) := by
  subst hR
  -- the core theorem at `N`
  have core := fun (N : Nat)
      (heN : ActEntryPRN vcp rf af fa fb K F G' XI H base ra' Kp' cc' P' Rr' t0 w₀' N) =>
    backend_twoRunLERWZNp (R := actRL vcp rf af fa fb lm base s (XI.upTo N) H psF K G (GotV vcp))
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
          (prologueSteps af.saves af.frameSize af.isCaller + T) = N := by
        rw [callsBefore_eq_countIn]; exact hc2
      have hcs : CallPc fa base (Arm.r .PC (runX (ArmStepX (XI.at 0) H fa)
          (prologueSteps af.saves af.frameSize af.isCaller + T) t0)) := by
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

end

end E2E
