import FV.E2E.PairDriverIG
import FV.E2E.PairDriverD
import FV.E2E.PairEntryD

/-!
# Non-interference of the counted VCode run, reads guarded (SEM1 #537, #699)

`vcode_niIG` (`PairDriverIG.lean`) on the guarded paired semantics `pairSemD`
(`PairGuardS.lean`): the paired counted run from the paired initial configuration is a run of
`ISem.counted fun n => pairSemD (csem F ctx (XI.at n)) F ctx (XI.at n)`, so at every step the
reads of the instruction avoid a set containing `F` and every byte where the two worlds differ
(`PGuard`). Same proof, on the guarded contracts (`instCalls_pairD`, …, `entry_step2PD`).

* `ncIndep_pairD`, `noCallProj_pairD`;
* **`vcode_niID`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- `pairSemD` at an instruction depends only on the semantics and `csem` there. -/
theorem pairSemD_congr {sem sem' : Sem} {F : BitVec 64 → Prop} {ctx : FnCtx} {X X' : ExtSem}
    {i : MInst} (hs : sem i = sem' i) (hc : ∀ Y, csem Y ctx X i = csem Y ctx X' i) :
    pairSemD sem F ctx X i = pairSemD sem' F ctx X' i := by
  have hg : ∀ us p, PGuard F ctx X i us p ↔ PGuard F ctx X' i us p := by
    intro us p; simp only [PGuard, RdOk, hc]
  have hp : ∀ us p, pairSem sem i us p = pairSem sem' i us p := by
    intro us p; simp only [pairSem, hs]
  funext us p
  by_cases hP : PGuard F ctx X i us p
  · rw [pairSemD_of hP, pairSemD_of ((hg us p).1 hP), hp]
  · simp only [pairSemD, if_neg hP, if_neg (mt (hg us p).2 hP)]

/-- The guarded paired family: the non-calls do not read the call number. -/
theorem ncIndep_pairD (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) :
    NcIndep (fun n => pairSemD (csem F ctx (XI.at n)) F ctx (XI.at n)) := by
  intro m n i h
  exact pairSemD_congr (csem_at_noncall F ctx XI h m n) fun Y => csem_at_noncall Y ctx XI h m n

/-- The guarded paired probes (calls failing) project into the counted guarded semantics. -/
theorem noCallProj_pairD (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) :
    NoCallProj (fun n => pairSemD (csem F ctx (XI.at n)) F ctx (XI.at n))
      (fun n => pairSemD (csem F ctx (XI.at n).noCall) F ctx (XI.at n).noCall) := by
  intro n i uses w outs w' ctl h
  cases hc : i.isCallI with
  | false =>
    have he : ∀ Y, csem Y ctx (XI.at n).noCall i = csem Y ctx (XI.at n) i := fun Y =>
      csem_call_congr Y ctx (XI.at n) _ hc
    have he2 : pairSemD (csem F ctx (XI.at n).noCall) F ctx (XI.at n).noCall i =
        pairSemD (csem F ctx (XI.at n)) F ctx (XI.at n) i := pairSemD_congr (he F) he
    simp only at h
    rw [he2] at h
    rw [counted_noncall (ncIndep_pairD F ctx XI) hc uses w n n, h]
    rfl
  | true =>
    have h' := (pairSemD_sub h).2
    simp [pairSem, csem_noCall_call hc] at h'

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- **Non-interference of the counted VCode run, reads guarded** (module doc; `vcode_niIG`'s
premises and conclusion, the run in `pairSemD`). -/
theorem vcode_niID (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
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
        VRetFrom vc (ISem.counted fun n =>
            pairSemD (csem F ⟨fa.k, af.slotBase⟩ (XI.at n)) F ⟨fa.k, af.slotBase⟩ (XI.at n))
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
      DriverHyp f vc ctx st0 R gn bl A
        (pairSemD (csem F ⟨fa.k, af.slotBase⟩ X) F ⟨fa.k, af.slotBase⟩ X) (MRP Γ f c D) env' p :=
    fun H hX' hXI' hsym' hNI' hTls' => {
      shape := hshape
      cert := hcert
      dsem := driverSemG_pairD F ⟨fa.k, af.slotBase⟩ _
      insts := instCalls_pairD hc hX' hXI' hsym' hslot hNI' hTls'
      terms := termCalls_pairD Γ rfl hTls' ⟨fa.k, af.slotBase⟩
      ext := H.ext
      indSig := H.indSig
      subE := H.subE
      entryLocs := H.entryLocs
      brIdx := H.brIdx
      noTail := H.noTail
      tries := ⟨_, tryCalls_pairD hc hX' hsym' hslot hNI' hTls',
        tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
      tryExt := H.tryExt
      tryInd := tryIndCalls_pairD hc hXI' hsym' hNI' hTls'
      tryIndSig := H.tryIndSig
      cfg := H.cfg }
  have HbP : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (pairSemD (csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall) F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (MRP Γ f c D) (env.only fun _ _ _ => False) p := fun n =>
    mkP (Hb1 n) (xCallsOk_none _ _ _ _) (xCallsIndOk_none _ _ _ _) hsym (xNI_noCall _) (hTls n)
  have HsP : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (pairSemD (csem F ⟨fa.k, af.slotBase⟩ (XI.at n)) F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (MRP Γ f c D) (env.only (Clif.Invoked env p s)) p := fun s n hr =>
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
  obtain ⟨kk, ρ₁, w₁, w₁', -, hm1, hsw1, -, hm2, hsw2, hsP⟩ := entry_step2PD (Hb1 0)
    (driverSem_csem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_csem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c) rfl hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmP : Match f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ := by
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w₁ w₁' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  have hR := sim_runIG (ncIndep_pairD F ⟨fa.k, af.slotBase⟩ XI)
    (noCallProj_pairD F ⟨fa.k, af.slotBase⟩ XI) hP HbP HsP hseg htc fuel cs 0 0 kk ρ₁ (w₁, w₁')
    .refl hmP
  rw [hrun] at hR
  obtain ⟨us, outs, w, cm0, -, hret, -, -, -, -, hmr, -⟩ := hR
  exact ⟨us, outs, w, VRetFrom.prefix (vstar_mapW (noCallProj_pairD F ⟨fa.k, af.slotBase⟩ XI 0) hsP)
    hret, SameWorld.mono (zof_sub cm0) hmr.2.2⟩

end

end E2E
