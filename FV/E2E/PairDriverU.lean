import FV.E2E.PairRaise
import FV.E2E.IselSimU
import FV.Backend.Proof.LowerSimUCheck
import FV.Backend.Proof.CleanupStageU
import FV.Backend.Proof.LowerSimSkipUW

/-!
# Non-interference of a compiled function's VCode run with unwinding (S10f, #233)

`PairDriver.vcode_ni` / `DeadCleanupPair.vcode_ni_value` for the CLIF runs with unwinding
(`Clif.runLoopX`) and the semantics with unwinding (`csemU`, `valueSemU`): two body-entry worlds
related to the same CLIF entry, agreeing outside `F ∪ D`, with the same argument registers and
stack-passed argument bytes, give one VCode outcome — for a returning CLIF run the same `rets`
with the same values, for an exceptional one the same raising call with the same exception
object — with final worlds that agree outside `F ∪ D`.

The generic driver with unwinding (`sim_runXW`) runs on the pairs of worlds: the normal-edge
contracts are `PairDriver`'s / `DeadCleanupPair`'s for `pairSem csem` / `pairSem valueSem`,
carried to the semantics with unwinding by monotonicity (`DriverHyp.sub`; a step of `csem` is
one of `csemU` under the callees' exclusivity), the raising code's contracts are
`raiseHypW_pair_csemU` / `raiseHypW_pair_valueSemU` (`FV/E2E/PairRaise.lean`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-! ## Monotonicity of the driver's contracts in the semantics -/

section
variable {V W : Type} {sem sem' : ISem V W}

theorem seqRun_sub (hsub : ∀ i us w r, sem i us w = some r → sem' i us w = some r) :
    ∀ (ms : List MInst) (ρ : Nat → V) (w : W) (e : SeqEnd V W),
      seqRun sem ms ρ w = some e → seqRun sem' ms ρ w = some e
  | [], _, _, _, h => h
  | i :: ms, ρ, w, e, h => by
    simp only [seqRun] at h ⊢
    cases hops : i.operands with
    | error => simp [hops] at h
    | ok ops =>
      simp only [hops] at h ⊢
      cases hs : sem i (vuses ops ρ) w with
      | none => simp [hs] at h
      | some r =>
        rw [hs] at h
        rw [hsub _ _ _ _ hs]
        obtain ⟨outs, w', ctl⟩ := r
        simp only at h ⊢
        by_cases hl : outs.length = (ops.toList.filter Operand.isDef).length
        · rw [if_pos hl] at h ⊢
          cases ctl with
          | next =>
            simp only at h ⊢
            cases hr : seqRun sem ms (vdefUpd ops outs ρ) w' with
            | none => rw [hr] at h; cases h
            | some e' =>
              rw [hr] at h
              rw [seqRun_sub hsub ms _ _ e' hr]
              exact h
          | _ => exact h
        · rw [if_neg hl] at h; cases h

end

section
variable {W : Type} {sem sem' : ISem CV W} {MR : MemRelTW W} {env : Clif.Env} {p : Clif.Program}
  {ctx : Ctx}

theorem _root_.Backend.Proof.LowerInstOk.sub (hsub : ∀ i us w r, sem i us w = some r → sem' i us w = some r)
    {inst : Clif.Inst} {results : List Nat} {st : LState} {rss : List (List Reg)} {st' : LState}
    {ms : List MInst} (h : LowerInstOk sem MR env p ctx inst results st rss st' ms) :
    LowerInstOk sem' MR env p ctx inst results st rss st' ms := by
  refine ⟨h.mono, h.defs, fun fr cm ρ w a b c d => ?_⟩
  have r := h.run fr cm ρ w a b c d
  revert r
  rcases instOutcome env p fr cm inst with ⟨vals, cm'⟩ | c0 | m <;> intro r
  · obtain ⟨hU, ρ', w', hs, hr, hm⟩ := r
    exact ⟨hU, ρ', w', seqRun_sub hsub _ _ _ _ hs, hr, hm⟩
  · intro hx
    obtain ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, hs, htc⟩ := r hx
    exact ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, seqRun_sub hsub _ _ _ _ hs, htc⟩
  · trivial

theorem _root_.Backend.Proof.LowerTermOk.sub (hsub : ∀ i us w r, sem i us w = some r → sem' i us w = some r)
    {t : Clif.Terminator} {targets : List Label} {st st' : LState} {ms : List MInst}
    (h : LowerTermOk sem MR ctx t targets st st' ms) : LowerTermOk sem' MR ctx t targets st st' ms := by
  refine ⟨h.mono, h.defs, fun fr cm ρ w a b c d => ?_⟩
  have r := h.run fr cm ρ w a b c d
  revert r
  cases t
  all_goals dsimp only
  all_goals first
    | (intro r vals hv
       obtain ⟨hU, k, us, ops, ρ₁, w₁, outs, w₂, hs, h1, h2, h3, hm⟩ := r vals hv
       exact ⟨hU, k, us, ops, ρ₁, w₁, outs, w₂, seqRun_sub hsub _ _ _ _ hs, h1, h2, h3, hm⟩)
    | (intro r
       obtain ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, hs, htc⟩ := r
       exact ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, seqRun_sub hsub _ _ _ _ hs, htc⟩)
    | (intro r
       refine ⟨r.1, fun j hj => ?_⟩
       obtain ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, hs, hk, hm⟩ := r.2 j hj
       exact ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, seqRun_sub hsub _ _ _ _ hs, hk, hm⟩)

theorem _root_.Backend.Proof.LowerTryOk.sub (hsub : ∀ i us w r, sem i us w = some r → sem' i us w = some r)
    {ci : Clif.Inst} {info : TryInfo} {st st' : LState} {ms : List MInst}
    (h : LowerTryOk sem MR env p ctx ci info st st' ms) :
    LowerTryOk sem' MR env p ctx ci info st st' ms := by
  refine ⟨h.mono, h.shape, fun fr cm ρ w a b c d => ?_⟩
  have r := h.run fr cm ρ w a b c d
  revert r
  rcases instOutcome env p fr cm ci with ⟨vals, cm'⟩ | c0 | m <;> intro r
  · obtain ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, hs, hk, hres, hm⟩ := r
    exact ⟨hU, k, i, ops, ρ₁, w₁, outs, w₂, seqRun_sub hsub _ _ _ _ hs, hk, hres, hm⟩
  · trivial
  · trivial

/-- **The driver's hypotheses are monotone in the semantics**: those of `sem` hold of a
semantics `sem'` with every step of `sem` (and the driver's world-independent facts). -/
theorem _root_.Backend.Proof.Driver.DriverHyp.sub {f : Clif.Function} {vc : VCode} {st0 : LState} {R : Reg → Reg}
    {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    (H : DriverHyp f vc ctx st0 R gn bl A sem MR env p)
    (hsub : ∀ i us w r, sem i us w = some r → sem' i us w = some r) (hds : DriverSemG sem') :
    DriverHyp f vc ctx st0 R gn bl A sem' MR env p := by
  obtain ⟨out, ht, hts⟩ := H.tries
  exact { H with
    dsem := hds
    insts := fun ctx ii info inst st rss st' tr a b c d e f g h i =>
      (H.insts ctx ii info inst st rss st' tr a b c d e f g h i).sub hsub
    terms := fun f ctx ti t data targets out st st' tr a b c d e g h i =>
      (H.terms f ctx ti t data targets out st st' tr a b c d e g h i).sub hsub
    tries := ⟨out, fun ctx ti fn args et data sig items targets info trs lo st1 o st' tr a b c d e g
        h i j => (ht ctx ti fn args et data sig items targets info trs lo st1 o st' tr a b c d e g
          h i j).sub hsub, hts⟩
    tryInd := fun f ctx ti callee args et data sig items targets info trs lo st1 o st' tr a b c d e g
        h i j k => (H.tryInd f ctx ti callee args et data sig items targets info trs lo st1 o st'
          tr a b c d e g h i j k).sub hsub }

end

theorem pairSem_sub {sem sem' : Sem} (hsub : ∀ i us w r, sem i us w = some r → sem' i us w = some r) :
    ∀ i us q r, pairSem sem i us q = some r → pairSem sem' i us q = some r := by
  intro i us q r h
  obtain ⟨o, q', c⟩ := r
  obtain ⟨h1, h2⟩ := pairSem_inv h
  exact pairSem_eq (hsub _ _ _ _ h1) (hsub _ _ _ _ h2)

/-- The paired semantics with unwinding satisfies the driver's world-independent facts. -/
theorem driverSemG_pair_of {sem : Sem} (hd : DriverSem sem) : DriverSemG (pairSem sem) where
  jump := fun l q => pairSem_eq (hd.jump l q.1) (hd.jump l q.2)
  rename := by
    intro g gn hg i
    funext us q
    simp only [pairSem]
    rw [hd.rename g gn hg i]
  retarget := by
    intro i ls i' h
    funext us q
    simp only [pairSem]
    rw [hd.retarget i ls i' h]

/-! ## Non-interference of the VCode run with unwinding -/

section
variable {p : Clif.Program} {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
  {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
  {semU : Sem} {XR : XRaise} {env : Clif.XEnv} {F : BitVec 64 → Prop}
  {syms : String → Option Nat} {slotOff ib : Nat} {c : BitVec 64} {D : BitVec 64 → Prop}
  {out : Nat}

/-- **Non-interference of the VCode run with unwinding, from the driver's hypotheses** (on one
world and on pairs of worlds), for `vcK`, the lowering `vc` or its kept code (`SkipHyp`). -/
theorem vcode_niU_core_of {vcK : VCode} {drop : Nat → Nat → Bool}
    (H : DriverHyp f vc ctx st0 R gn bl A semU (RelW ⟨F, syms, slotOff, ib⟩ f c) env.toEnv p)
    (HP : DriverHyp f vc ctx st0 R gn bl A (pairSem semU) (MRP ⟨F, syms, slotOff, ib⟩ f c D)
      env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A)
    (HR : RaiseHypW f (pairSem semU) (pairRaise XR) (MRP ⟨F, syms, slotOff, ib⟩ f c D) env p out)
    (hds : DriverSem semU) (hmem : MemRefines F slotOff syms semU)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState}
    (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, ib⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, ib⟩ f c cs.frame.slots cs.mem w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w w', VReturns vcK semU ρ₀ w₀ us outs w ∧ VReturns vcK semU ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w') ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w w', VUnwinds vcK semU XR ρ₀ w₀ obj w ∧ VUnwinds vcK semU XR ρ₀ w₀' obj w' ∧
        SameWorld (fun b => F b ∨ D b) w w') := by
  let Γ : Rel := ⟨F, syms, slotOff, ib⟩
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀ := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨kk, ρ₁, w₁, w₁', hs1, hm1, hsw1, hs2, hm2, hsw2⟩ := entry_step2P H hds hmem
    (mrStable_relW Γ f c) hB0 hce.callers hce.func rfl hbody hterm hregs hty.symm hce.sig
    (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmP : Match f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ := by
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w₁ w₁' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  rcases hsk with rfl | hK
  · have hR := sim_runXW HP HU HR hce.func htr fuel cs.toX _ (.refl _) hmP
    refine ⟨fun vals cm hrun => ?_, fun e cm hrun => ?_⟩
    · rw [hrun] at hR
      obtain ⟨us, outs, w, cm0, hret, -, -, -, hmr, -⟩ := hR
      obtain ⟨h1, h2⟩ := vRetFrom_pair hret
      exact ⟨us, outs, w.1, w.2, VRetFrom.prefix hs1.star h1, VRetFrom.prefix hs2.star h2,
        SameWorld.mono (zof_sub cm0) hmr.2.2⟩
    · rw [hrun] at hR
      obtain ⟨obj, w, cm0, hu, -, hmr, -⟩ := hR
      obtain ⟨h1, h2⟩ := vUnwFrom_pair hu
      exact ⟨obj, w.1, w.2, VUnwFrom.prefix hs1.star h1, VUnwFrom.prefix hs2.star h2,
        SameWorld.mono (zof_sub cm0) hmr.2.2⟩
  · have hkk := entry_pos hB0 hbody hm1
    have hs1K := entry_runK hK hB0 hkk hs1
    have hs2K := entry_runK hK hB0 hkk hs2
    have hR := sim_runXWK HP HU HR hK hce.func htr fuel cs.toX
      ⟨0, kidx (skipMask f R bl vc drop 0) kk, ρ₁, (w₁, w₁')⟩ (.refl _)
      ⟨⟨0, kk, ρ₁, (w₁, w₁')⟩, ⟨rfl, rfl, rfl, fun _ _ => rfl⟩, hmP⟩
    refine ⟨fun vals cm hrun => ?_, fun e cm hrun => ?_⟩
    · rw [hrun] at hR
      obtain ⟨us, outs, w, cm0, hret, -, -, -, hmr, -⟩ := hR
      obtain ⟨h1, h2⟩ := vRetFrom_pair hret
      exact ⟨us, outs, w.1, w.2, VRetFrom.prefix hs1K h1, VRetFrom.prefix hs2K h2,
        SameWorld.mono (zof_sub cm0) hmr.2.2⟩
    · rw [hrun] at hR
      obtain ⟨obj, w, cm0, hu, -, hmr, -⟩ := hR
      obtain ⟨h1, h2⟩ := vUnwFrom_pair hu
      exact ⟨obj, w.1, w.2, VUnwFrom.prefix hs1K h1, VUnwFrom.prefix hs2K h2,
        SameWorld.mono (zof_sub cm0) hmr.2.2⟩

/-- **Non-interference of the VCode run with unwinding, from the driver's hypotheses** (on one
world and on pairs of worlds). -/
theorem vcode_niU_core
    (H : DriverHyp f vc ctx st0 R gn bl A semU (RelW ⟨F, syms, slotOff, ib⟩ f c) env.toEnv p)
    (HP : DriverHyp f vc ctx st0 R gn bl A (pairSem semU) (MRP ⟨F, syms, slotOff, ib⟩ f c D)
      env.toEnv p)
    (HU : UnwShape f vc ctx R gn bl A)
    (HR : RaiseHypW f (pairSem semU) (pairRaise XR) (MRP ⟨F, syms, slotOff, ib⟩ f c D) env p out)
    (hds : DriverSem semU) (hmem : MemRefines F slotOff syms semU)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState}
    (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, ib⟩ f c cs.frame.slots cs.mem w₀)
    (hrel' : RelW ⟨F, syms, slotOff, ib⟩ f c cs.frame.slots cs.mem w₀')
    (hargs : ArgsAtEntry F f.sig args w₀)
    (hsw : SameWorld (fun b => F b ∨ D b) w₀ w₀')
    (hreg : ∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r)
    (hstk : ∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
      w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
        w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k))
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w w', VReturns vc semU ρ₀ w₀ us outs w ∧ VReturns vc semU ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w') ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w w', VUnwinds vc semU XR ρ₀ w₀ obj w ∧ VUnwinds vc semU XR ρ₀ w₀' obj w' ∧
        SameWorld (fun b => F b ∨ D b) w w') :=
  vcode_niU_core_of (drop := fun _ _ => false) H HP HU HR hds hmem (.inl rfl) ρ₀ hce hrel hrel'
    hargs hsw hreg hstk htr fuel

end

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- **Non-interference of a compiled function's VCode run with unwinding** (legacy pipeline,
`csemU`): `vcode_ni` for the runs with unwinding — a returning CLIF run gives the same `rets`
and values, an exceptional one the same exception object, on two body-entry worlds that agree
outside `F ∪ D` (under the callees' non-interference on returns `XNI` and on raises `XRNI`),
with final worlds that agree outside `F ∪ D`. -/
theorem vcode_niU (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    (hRNI : XRNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
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
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w w', VReturns vc (csemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀ us outs w ∧
        VReturns vc (csemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w') ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w w', VUnwinds vc (csemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀ obj w ∧
        VUnwinds vc (csemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀' obj w' ∧
        SameWorld (fun b => F b ∨ D b) w w') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUs⟩ := loweringU_of_check hlU
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (csem F ⟨fa.k, af.slotBase⟩ X) := refines_csem _ _ X
  have hmem : MemRefines F slotOff syms (csem F ⟨fa.k, af.slotBase⟩ X) :=
    memRefines_csem _ _ X hslot hsym
  have hcalls := callsRefine_csem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX
  have hicalls := indCallsRefine_csem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols)
  have houtB := outgoing_le_intBase hc
  have H : DriverHyp f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ X) (RelW Γ f c)
      env.toEnv p := {
    shape := hshape
    cert := hcert
    dsem := (driverSem_csem F ⟨fa.k, af.slotBase⟩ X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := cfg_of_prepare hc.prepare }
  have HP : DriverHyp f vc ctx st0 R gn bl A (pairSem (csem F ⟨fa.k, af.slotBase⟩ X)) (MRP Γ f c D)
      env.toEnv p := {
    shape := hshape
    cert := hcert
    dsem := driverSemG_pair F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_pair hc hX hXI hsym hslot hNI hTls
    terms := termCalls_pair Γ rfl hTls ⟨fa.k, af.slotBase⟩
    ext := H.ext
    indSig := H.indSig
    subE := H.subE
    entryLocs := H.entryLocs
    brIdx := H.brIdx
    noTail := H.noTail
    tries := ⟨_, tryCalls_pair hc hX hsym hslot hNI hTls,
      tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := H.tryExt
    tryInd := tryIndCalls_pair hc hXI hsym hNI hTls
    tryIndSig := H.tryIndSig
    cfg := H.cfg }
  have hsubU : ∀ i us w r, csem F ⟨fa.k, af.slotBase⟩ X i us w = some r →
      csemU F ⟨fa.k, af.slotBase⟩ X XR i us w = some r := fun _ _ _ _ h => csemU_of_csem hexcl h
  have hdU := driverSem_csemU F ⟨fa.k, af.slotBase⟩ X XR
  exact vcode_niU_core (H.sub hsubU hdU.toDriverSemG) (HP.sub (pairSem_sub hsubU)
      (driverSemG_pair_of hdU)) hUs
    (raiseHypW_pair_csemU (D := D) (p := p) ⟨fa.k, af.slotBase⟩ hslot hTls hexcl
      (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (tryStack_mono (tryStack_of_check hc.lowerOk) houtB) (outArgsOk_relW Γ f c) hXR hXRi hsym
      hRNI)
    hdU (memRefines_csemU _ _ X XR hslot hsym) ρ₀ hce hrel hrel' hargs hsw hreg hstk htr fuel

/-- `vcode_niU_value` for `vcK`, the lowering `vc` or its kept code (`SkipHyp`), from the lowering
obligations of `vc` with its `UnwShape`. -/
theorem vcode_niU_value_of {vcK : VCode} (hsub : InSubset p f)
    (hc : CompiledCleanup f k vc vcp rf af fa fb)
    {ctx : Ctx} {st0 : LState} {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow}
    {A : Nat → Nat → List Clif.ValueId} {drop : Nat → Nat → Bool}
    (hshape : LowerShape f vc ctx st0 R gn bl) (hcert : Cert f ctx st0 gn bl A)
    (hbr : ∀ B ∈ f.blocks, BrIdxTyped ctx B.term) (hUs : UnwShape f vc ctx R gn bl A)
    (hsk : vcK = vc ∨ SkipHyp f vc R bl drop vcK)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    (hRNI : XRNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
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
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w w', VReturns vcK (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀ us outs w ∧
        VReturns vcK (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w') ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w w', VUnwinds vcK (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀ obj w ∧
        VUnwinds vcK (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀' obj w' ∧
        SameWorld (fun b => F b ∨ D b) w w') := by
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have hRef : Refines F (valueSem F ⟨fa.k, af.slotBase⟩ X) := refines_valueSem _ _ X
  have hmem : MemRefines F slotOff syms (valueSem F ⟨fa.k, af.slotBase⟩ X) :=
    memRefines_valueSem _ _ X hslot hsym
  have hcalls := callsRefine_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hX
  have hicalls := indCallsRefine_valueSem (F := F) (ctx := ⟨fa.k, af.slotBase⟩) hXI hsym
    (fun _ _ _ h => h.1.1.symbols)
  have houtB := outgoing_le_intBaseCleanupA hc.toA
  have H : DriverHyp f vc ctx st0 R gn bl A (valueSem F ⟨fa.k, af.slotBase⟩ X) (RelW Γ f c)
      env.toEnv p := {
    shape := hshape
    cert := hcert
    dsem := (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ X).toDriverSemG
    insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
      indRulesCorrect memRulesCorrect_program hRef (mrStable_relW Γ f c) hcalls hicalls hmem
      (outArgsOk_relW Γ f c) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (memRelOk_relW Γ f c)
    terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
      branchExcludedUnmatchable hRef (mrStable_relW Γ f c)
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨_, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_relW Γ f c) hmem
      (outArgsOk_relW Γ f c) hcalls, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef (mrStable_relW Γ f c)
      hicalls
    tryIndSig := tryIndSig_of_subset hsub
    cfg := by
      obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
      exact ⟨ss, ps, (cleanupStage_cfg f vc).symm.trans he⟩ }
  have HP : DriverHyp f vc ctx st0 R gn bl A (pairSem (valueSem F ⟨fa.k, af.slotBase⟩ X))
      (MRP Γ f c D) env.toEnv p := {
    shape := hshape
    cert := hcert
    dsem := driverSemG_pair_value F ⟨fa.k, af.slotBase⟩ X
    insts := instCalls_pair_value hc hX hXI hsym hslot hNI hTls
    terms := termCalls_pair_value Γ rfl hTls ⟨fa.k, af.slotBase⟩
    ext := H.ext
    indSig := H.indSig
    subE := H.subE
    entryLocs := H.entryLocs
    brIdx := H.brIdx
    noTail := H.noTail
    tries := ⟨_, tryCalls_pair_value hc hX hsym hslot hNI hTls,
      tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := H.tryExt
    tryInd := tryIndCalls_pair_value hc hXI hsym hNI hTls
    tryIndSig := H.tryIndSig
    cfg := H.cfg }
  have hsubU : ∀ i us w r, valueSem F ⟨fa.k, af.slotBase⟩ X i us w = some r →
      valueSemU F ⟨fa.k, af.slotBase⟩ X XR i us w = some r :=
    fun _ _ _ _ h => valueSemU_of_valueSem hexcl h
  have hdU := driverSem_valueSemU F ⟨fa.k, af.slotBase⟩ X XR
  exact vcode_niU_core_of (H.sub hsubU hdU.toDriverSemG) (HP.sub (pairSem_sub hsubU)
      (driverSemG_pair_of hdU)) hUs
    (raiseHypW_pair_valueSemU (D := D) (p := p) ⟨fa.k, af.slotBase⟩ hslot hTls hexcl
      (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (tryStack_mono (tryStack_of_check hc.lowerOk) houtB) (outArgsOk_relW Γ f c) hXR hXRi hsym
      hRNI)
    hdU (memRefines_valueSemU _ _ X XR hslot hsym) hsk ρ₀ hce hrel hrel' hargs hsw hreg hstk htr
    fuel

/-- **Non-interference of a compiled function's VCode run with unwinding** (the shipped
dead-cleanup pipeline, `valueSemU`). -/
theorem vcode_niU_value (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    (hRNI : XRNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
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
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w w', VReturns vc (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀ us outs w ∧
        VReturns vc (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w') ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w w', VUnwinds vc (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀ obj w ∧
        VUnwinds vc (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀' obj w' ∧
        SameWorld (fun b => F b ∨ D b) w w') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUs⟩ := loweringU_of_check hlU
  exact vcode_niU_value_of (drop := fun _ _ => false) hsub hc hshape hcert hbr hUs (.inl rfl) hX
    hXI hXR hXRi hexcl hsym hslot hNI hTls hRNI ρ₀ hce hrel hrel' hargs hsw hreg hstk htr fuel

/-- **`vcode_niU_value` for the code after the skip of unused instructions** (`skipStage f vc`). -/
theorem vcode_niU_value_stage (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {XR : XRaise} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hX : XCallsOk env.toEnv (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env.toEnv (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXR : XRaiseOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hXRi : XRaiseIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X XR)
    (hexcl : ∀ d uses w, X.call d uses w ≠ none → XR.raise d uses w = none)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg env.toEnv (f.externs.map (·.2)) (indSigs f)) X) (hTls : XTls F X)
    (hRNI : XRNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLgR env (f.externs.map (·.2)) (indSigs f)) X XR)
    {args : List Clif.Val} {cs : Clif.State} {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
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
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoopX env p fuel cs.toX = .returned vals cm →
      ∃ us outs w w', VReturns (skipStage f vc) (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀ us
          outs w ∧
        VReturns (skipStage f vc) (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) ρ₀ w₀' us outs w' ∧
        SameWorld (fun b => F b ∨ D b) w w') ∧
    (∀ e cm, Clif.runLoopX env p fuel cs.toX = .unwound e cm →
      ∃ obj w w', VUnwinds (skipStage f vc) (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀ obj w ∧
        VUnwinds (skipStage f vc) (valueSemU F ⟨fa.k, af.slotBase⟩ X XR) XR ρ₀ w₀' obj w' ∧
        SameWorld (fun b => F b ∨ D b) w w') := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUs, hsk⟩ := skipStage_specU hlU
  exact vcode_niU_value_of hsub hc hshape hcert hbr hUs hsk hX hXI hXR hXRi hexcl hsym hslot hNI
    hTls hRNI ρ₀ hce hrel hrel' hargs hsw hreg hstk htr fuel

end

end E2E
