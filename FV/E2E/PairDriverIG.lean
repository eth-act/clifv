module

public import FV.E2E.IselSimIG
public import FV.E2E.PairDriver
public import FV.E2E.PairEntry

@[expose] public section

/-!
# Non-interference of the counted VCode run (SEM1 #537, item (3))

`vcode_ni` (`PairDriver.lean`) for the counted semantics: the driver simulation (`sim_runIG`) on
the counted paired semantics `ISem.counted fun n => pairSem (csem F ctx (XI.at n))` (both worlds,
one call counter), with the callee contracts and their non-interference needed only for the
actual `n`-th call of the run (as `iselSim_relWI`). Two body-entry worlds related to the same CLIF
entry, agreeing outside `F ∪ D` with the same arguments, give one paired counted VCode run from
the paired initial configuration (the entry code paired by `entry_step2P`) that returns, with
final worlds that agree outside `F ∪ D`.

* `ncIndep_pair`, `noCallProj_pair`, `xNI_noCall`;
* **`vcode_niIG`** (named apart from the `vcode_niI` of `agent/uninit-z16b`, which runs
  `sim_runG` on `csemI`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- The paired `csem` family: the non-calls do not read the call number. -/
theorem ncIndep_pair (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) :
    NcIndep (fun n => pairSem (csem F ctx (XI.at n))) := by
  intro m n i h
  funext us w
  simp only [pairSem, csem_at_noncall F ctx XI h m n]

/-- The paired probes (calls failing) project into the counted paired semantics. -/
theorem noCallProj_pair (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) :
    NoCallProj (fun n => pairSem (csem F ctx (XI.at n)))
      (fun n => pairSem (csem F ctx (XI.at n).noCall)) := by
  intro n i uses w outs w' ctl h
  cases hc : i.isCallI with
  | false =>
    have he : csem F ctx (XI.at n).noCall i = csem F ctx (XI.at n) i :=
      csem_call_congr F ctx (XI.at n) _ hc
    have he2 : pairSem (csem F ctx (XI.at n).noCall) i = pairSem (csem F ctx (XI.at n)) i := by
      funext us w; simp only [pairSem, he]
    simp only at h
    rw [he2] at h
    rw [counted_noncall (ncIndep_pair F ctx XI) hc uses w n n, h]
    rfl
  | true =>
    simp [pairSem, csem_noCall_call hc] at h

/-- Calls that fail are non-interfering. -/
theorem xNI_noCall {F : BitVec 64 → Prop} {syms : String → Option Nat} {exts : List Clif.ExtFunc}
    {sigs : List Clif.Signature} {sp0 : BitVec 64}
    {Lg : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} (X : ExtSem) :
    XNI F syms exts sigs sp0 Lg X.noCall := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h
  cases h

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- **Non-interference of the counted VCode run** (module doc). -/
theorem vcode_niIG (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
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
    {w₀ w₀' : Arm.ArmState} {D : BitVec 64 → Prop}
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
      ∃ us outs w,
        VRetFrom vc (ISem.counted fun n => pairSem (csem F ⟨fa.k, af.slotBase⟩ (XI.at n)))
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 := by
  intro vals cm hrun
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have houtB := outgoing_le_intBase hc
  have Hb1 : ∀ n, DriverHyp f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _) (xCallsIndOk_none _ _ _ _)
      hsym hslot
  have Hs1 : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (csem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2 hsym hslot
  have mkP : ∀ {X : ExtSem} {env' : Clif.Env},
      DriverHyp f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ X) (RelW Γ f c) env' p →
      XCallsOk env' (f.externs.map (·.2)) (RelW Γ f c) X →
      XCallsIndOk env' (indSigs f) (RelW Γ f c) X →
      (∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) →
      XNI F syms (f.externs.map (·.2)) (indSigs f) c (CallLg env' (f.externs.map (·.2)) (indSigs f))
        X → XTls F X →
      DriverHyp f vc ctx st0 R gn bl A (pairSem (csem F ⟨fa.k, af.slotBase⟩ X)) (MRP Γ f c D)
        env' p :=
    fun H hX' hXI' hsym' hNI' hTls' => {
      shape := hshape
      cert := hcert
      dsem := driverSemG_pair F ⟨fa.k, af.slotBase⟩ _
      insts := instCalls_pair hc hX' hXI' hsym' hslot hNI' hTls'
      terms := termCalls_pair Γ rfl hTls' ⟨fa.k, af.slotBase⟩
      ext := H.ext
      indSig := H.indSig
      subE := H.subE
      entryLocs := H.entryLocs
      brIdx := H.brIdx
      noTail := H.noTail
      tries := ⟨_, tryCalls_pair hc hX' hsym' hslot hNI' hTls',
        tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
      tryExt := H.tryExt
      tryInd := tryIndCalls_pair hc hXI' hsym' hNI' hTls'
      tryIndSig := H.tryIndSig
      cfg := H.cfg }
  have HbP : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (pairSem (csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)) (MRP Γ f c D)
      (env.only fun _ _ _ => False) p := fun n =>
    mkP (Hb1 n) (xCallsOk_none _ _ _ _) (xCallsIndOk_none _ _ _ _) hsym (xNI_noCall _) (hTls n)
  have HsP : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (pairSem (csem F ⟨fa.k, af.slotBase⟩ (XI.at n))) (MRP Γ f c D)
      (env.only (Clif.Invoked env p s)) p := fun s n hr =>
    mkP (Hs1 s n hr) (hX s n hr).1 (hX s n hr).2 hsym (hNI s n hr) (hTls n)
  have hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1 :=
    fun _ _ _ _ hB hstm hcl => segCalls_of (Hb1 0) hone hB hstm hcl
  obtain ⟨B0, hent, hbody, hterm, hty, hregs⟩ := hce.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hent
  have hP : RunPrem env p f cs := by
    have hf := hce.func
    exact ⟨htr.stmt, fun s c fn args et hr hs hb hT B hB => htr.tryCall s c fn args et hr hs hb hT B
        (hf ▸ hB),
      fun s c callee args et hr hs hb hT B hB =>
        htr.tryCallInd s c callee args et hr hs hb hT B (hf ▸ hB),
      fun s st rest sig callee args hr hb hi ⟨B, hB, hst⟩ =>
        htr.indirect s st rest sig callee args hr hb hi ⟨B, hf ▸ hB, hst⟩,
      fun s callee args et hr hb hT ⟨B, hB, e⟩ =>
        htr.tryIndirect s callee args et hr hb hT ⟨B, hf ▸ hB, e⟩⟩
  have h29 : Arm.r (.GPR 29#5) w₀' = Arm.r (.GPR 29#5) w₀ := (hsw.1 _ (by simp [Masked])).symm
  obtain ⟨kk, ρ₁, w₁, w₁', -, hm1, hsw1, -, hm2, hsw2, hsP⟩ := entry_step2P (Hb1 0)
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_csem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmP : Match f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ := by
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w₁ w₁' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  have hR := sim_runIG (ncIndep_pair F ⟨fa.k, af.slotBase⟩ XI)
    (noCallProj_pair F ⟨fa.k, af.slotBase⟩ XI) hP HbP HsP hseg htc fuel cs 0 0 kk ρ₁ (w₁, w₁')
    .refl hmP
  rw [hrun] at hR
  obtain ⟨us, outs, w, cm0, -, hret, -, -, -, -, hmr, -⟩ := hR
  exact ⟨us, outs, w, VRetFrom.prefix (vstar_mapW (noCallProj_pair F ⟨fa.k, af.slotBase⟩ XI 0) hsP)
    hret, SameWorld.mono (zof_sub cm0) hmr.2.2⟩

end

end E2E
