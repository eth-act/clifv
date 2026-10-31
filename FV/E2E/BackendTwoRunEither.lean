import FV.E2E.BackendPairRunDF
import FV.E2E.BackendPairRunDCleanup
import FV.E2E.BackendTwoRunNIV
import FV.E2E.BackendTwoRunNIUP
import FV.E2E.CompiledEither

/-!
# The paired run and the two-run lock for either artifact (SEM1 #537, #713)

The link's functions are `CompiledEither` (`LinkSys.Ok.compiled`): the legacy path (`Compiled`,
`csemV` runs) or the shipped cleanup path (`CompiledCleanup`, value-semantics runs). Dispatch:

* **`backend_pairRunDF_either`**: the guarded paired run of `vcp` from `XNIF` (world difference
  inside `F`), in the legacy paired semantics (`backend_pairRunDF`) or in the value one
  (`backend_pairRunDF_cleanup`), each with its artifact;
* **`backend_twoRunLERWZIUF_either`**: the paired run and `backend_twoRunLERWZIU` /
  `backend_twoRunLERWZIUV` in one: from the CLIF run's return, the entries' premises and the lock
  premises (the same for both paths), the two activations return locked, with `RetAgreeX` and the
  memory outside `F ∪ D` equal; the semantics of the paired run does not appear;
* **`backend_twoRunLERWZIUPF_either`**: the same with `backend_twoRunLERWZIUP` /
  `backend_twoRunLERWZIUPV` (#729: `hcall` told the first run's segment start, both runs' facts
  at the return).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- **The guarded paired run for either artifact, from `XNIF`** (module doc). -/
theorem backend_pairRunDF_either (hsub : InSubset p f)
    (hc : CompiledEither f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hNI : ∀ s n, ReachN env p cs s n → XNIF F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f)) (XI.at n))
    (hTls : ∀ n, XTls F (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (hD : ∀ a, D a → F a)
    (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
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
      (Compiled f k vc vcp rf af fa fb ∧ ∃ us outs w,
        VRetFrom vcp (pairDI (csemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2) ∨
      (CompiledCleanup f k vc vcp rf af fa fb ∧ ∃ us outs w,
        VRetFrom vcp (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2) := by
  intro vals cm hrun
  cases hc with
  | legacy h =>
    exact .inl ⟨h, backend_pairRunDF hsub h hone htc hX hNI hTls hsym hslot hD ρ₀ hce hrel hrel'
      hargs hsw hreg hstk htr fuel vals cm hrun⟩
  | cleanup h =>
    exact .inr ⟨h, backend_pairRunDF_cleanup hsub h hone htc hX hNI hTls hsym hslot hD ρ₀ hce
      hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun⟩

set_option maxHeartbeats 4000000 in
/-- **The two-run lock for either artifact, from the CLIF run** (module doc):
`backend_pairRunDF_either` followed by `backend_twoRunLERWZIU` (legacy) or
`backend_twoRunLERWZIUV` (cleanup), whose premises other than the paired run coincide. -/
theorem backend_twoRunLERWZIUF_either (hsub : InSubset p f)
    (hc : CompiledEither f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hNI : ∀ s n, ReachN env p cs s n → XNIF F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f)) (XI.at n))
    (hTls : ∀ n, XTls F (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (hD : ∀ a, D a → F a)
    (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem
      w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicit env p cs) (fuel : Nat) {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm)
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
  rcases backend_pairRunDF_either hsub hc hone htc hX hNI hTls hsym hslot hD ρ₀ hce hrel hrel' hargs
      hsw hreg hstk htr fuel vals cm hrun with
    ⟨h, us, outs, w, ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hk, hops, hvals, hsem⟩, -⟩ |
    ⟨h, us, outs, w, ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hk, hops, hvals, hsem⟩, -⟩
  · exact backend_twoRunLERWZIU h ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF he he0 hC' hT' hR hcov
      hx30 hcall htls hag hx29
  · exact backend_twoRunLERWZIUV h ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF he he0 hC' hT' hR hcov
      hx30 hcall htls hag hx29

set_option maxHeartbeats 4000000 in
/-- **The two-run lock for either artifact, `hcall` told the first run's segment start, both runs'
return facts** (#729): `backend_pairRunDF_either` followed by `backend_twoRunLERWZIUP` (legacy) or
`backend_twoRunLERWZIUPV` (cleanup). -/
theorem backend_twoRunLERWZIUPF_either (hsub : InSubset p f)
    (hc : CompiledEither f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hNI : ∀ s n, ReachN env p cs s n → XNIF F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f)) (XI.at n))
    (hTls : ∀ n, XTls F (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop} (hD : ∀ a, D a → F a)
    (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem
      w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicit env p cs) (fuel : Nat) {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm)
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
  rcases backend_pairRunDF_either hsub hc hone htc hX hNI hTls hsym hslot hD ρ₀ hce hrel hrel' hargs
      hsw hreg hstk htr fuel vals cm hrun with
    ⟨h, us, outs, w, ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hk, hops, hvals, hsem⟩, -⟩ |
    ⟨h, us, outs, w, ⟨b, kk, ρ, w₁, vb, ops, outs', hs, hvb, hk, hops, hvals, hsem⟩, -⟩
  · exact backend_twoRunLERWZIUP h ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF he he0 hC' hT' hR hcov
      hx30 hcall htls hag hx29
  · exact backend_twoRunLERWZIUPV h ρ₀ hsw hs hvb hk hops hvals hsem hlm hpsF he he0 hC' hT' hR hcov
      hx30 hcall htls hag hx29

end

end E2E
