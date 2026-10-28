import FV.E2E.PairDriver
import FV.E2E.IselSimITry

/-!
# Non-interference of the counted VCode run (SEM1, `docs/plans/uninit.md` §5.9)

`vcode_ni` (`FV/E2E/PairDriver.lean`) for the counted run `csemI F ctx XI`: the pair driver
(`pairSem`, `MRP`) runs per CLIF step with the contracts of the step's call index, the
environment restricted to the step's invocation (`sim_runG` on the family `pairSem (csem F ctx
(XI.at n))`, the probe with failing calls). The external semantics' non-interference (`XNI`) is
needed, like the callee contracts, only at the states the CLIF run reaches after `n` calls, for
`XI.at n` and the restricted environment.

* `ISem.counted_pair_proj₁`/`₂`: a counted pair run projects to the counted run of each world;
* `noncallIndep_pair`, `probeOf_pair`; `xNI_none` (the environment answering nothing admits no
  call);
* **`vcode_niI`**.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-! ## Counted pairs -/

section
variable {sem : Nat → Sem}

theorem counted_pair_proj₁ :
    ISem.ProjW (fun q : W2 × Nat => (q.1.1, q.2)) (ISem.counted fun n => pairSem (sem n))
      (ISem.counted sem) := by
  intro i uses w outs w' ctl h
  obtain ⟨h1, h2⟩ := ISem.counted_some h
  obtain ⟨g1, -⟩ := pairSem_inv h1
  simp only [ISem.counted, g1, Option.map_some, h2]

theorem counted_pair_proj₂ :
    ISem.ProjW (fun q : W2 × Nat => (q.1.2, q.2)) (ISem.counted fun n => pairSem (sem n))
      (ISem.counted sem) := by
  intro i uses w outs w' ctl h
  obtain ⟨h1, h2⟩ := ISem.counted_some h
  obtain ⟨-, g2⟩ := pairSem_inv h1
  simp only [ISem.counted, g2, Option.map_some, h2]

theorem noncallIndep_pair (h : NoncallIndep sem) : NoncallIndep fun n => pairSem (sem n) := by
  intro i hi m m'
  funext us p
  simp only [pairSem, h i hi m m']

theorem probeOf_pair {semB : Nat → Sem} (h : ProbeOf semB sem) :
    ProbeOf (fun n => pairSem (semB n)) (fun n => pairSem (sem n)) where
  noncall n i hi := by
    funext us p
    simp only [pairSem, h.noncall n i hi]
  call n i hi us p := by
    simp only [pairSem, h.call n i hi]

end

/-- The environment answering nothing admits no call (`XNI` holds vacuously). -/
theorem xNI_none (env : Clif.Env) (F : BitVec 64 → Prop) (syms : String → Option Nat)
    (exts : List Clif.ExtFunc) (sigs : List Clif.Signature) (sp0 : BitVec 64) (X : ExtSem) :
    XNI F syms exts sigs sp0 (CallLg (env.only fun _ _ _ => False) exts sigs) X := by
  intro n sig vals cm _ _ _ _ _ _ _ _ _ _ ⟨_, g, rv, cm', hg, hret⟩
  obtain ⟨g0, -, rfl⟩ := Clif.Env.only_extern_eq hg
  rw [Clif.onlyFn_of_not (fun h => h)] at hret
  cases hret

/-! ## Non-interference -/

/-- **Non-interference of a compiled function's counted VCode run** (`vcode_ni` for `csemI`):
two body-entry worlds related to the same CLIF entry, agreeing outside `F ∪ D`, with the same
argument registers and stack-passed argument bytes, return (for a returning CLIF run) through the
same `rets` with the same values and the same call count, final worlds that agree outside
`F ∪ D`; the callee contracts and `XNI` of call number `n` at the CLIF states reached after `n`
calls, for the environment restricted to their invocation. -/
theorem vcode_niI {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    (hNI : ∀ s n, ReachN env p cs s n → XNI F syms (f.externs.map (·.2)) (indSigs f) c
      (CallLg (env.only (Clif.Invoked env p s)) (f.externs.map (·.2)) (indSigs f)) (XI.at n))
    (hTls : XTls F (XI.at 0))
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
      ∃ us outs w w' nc, VRetFrom vc (csemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀, 0)⟩ us outs
          (w, nc) ∧
        VRetFrom vc (csemI F ⟨fa.k, af.slotBase⟩ XI) ⟨0, 0, ρ₀, (w₀', 0)⟩ us outs (w', nc) ∧
        SameWorld (fun b => F b ∨ D b) w w' := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have houtB := outgoing_le_intBase hc
  -- the single-world driver hypotheses of each index
  have H1 : ∀ (env' : Clif.Env) (X : ExtSem),
      XCallsOk env' (f.externs.map (·.2)) (RelW Γ f c) X →
      XCallsIndOk env' (indSigs f) (RelW Γ f c) X →
      (∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) →
      DriverHyp f vc ctx st0 R gn bl A (csem F ⟨fa.k, af.slotBase⟩ X) (RelW Γ f c) env' p :=
    fun env' X hX' hXI' hsym' => driverHyp_relW hsub hc hshape hcert hbr hX' hXI' hsym' hslot
  -- the pair driver hypotheses of each index
  have HP : ∀ (env' : Clif.Env) (X : ExtSem),
      XCallsOk env' (f.externs.map (·.2)) (RelW Γ f c) X →
      XCallsIndOk env' (indSigs f) (RelW Γ f c) X →
      (∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) →
      XNI F syms (f.externs.map (·.2)) (indSigs f) c
        (CallLg env' (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
      DriverHyp f vc ctx st0 R gn bl A (pairSem (csem F ⟨fa.k, af.slotBase⟩ X)) (MRP Γ f c D)
        env' p := fun env' X hX' hXI' hsym' hNI' hTls' =>
    let H := H1 env' X hX' hXI' hsym'
    { shape := hshape
      cert := hcert
      dsem := driverSemG_pair F ⟨fa.k, af.slotBase⟩ X
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
  have Hb : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (pairSem (csem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)) (MRP Γ f c D)
      (env.only fun _ _ _ => False) p := fun n =>
    HP _ _ (xCallsOk_none _ _ _ _) (xCallsIndOk_none _ _ _ _) hsym (xNI_none _ _ _ _ _ _ _) hTls
  have Hs : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (pairSem (csem F ⟨fa.k, af.slotBase⟩ (XI.at n))) (MRP Γ f c D)
      (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => HP _ _ (hX s n hr).1 (hX s n hr).2 hsym (hNI s n hr) hTls
  have hseg : ∀ b B j stm, f.blocks[b]? = some B → B.body[j]? = some stm →
      stm.inst.isCallLike = true → callsI (seg f R bl b j) = 1 :=
    fun _ _ _ _ hB hstm hcl => segCalls_of (Hb 0) hone hB hstm hcl
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
  have H0 := H1 _ _ (xCallsOk_none env _ _ (XI.at 0).noCall)
    (xCallsIndOk_none env _ _ (XI.at 0).noCall) hsym
  obtain ⟨kk, ρ₁, w₁, w₁', hs1, hm1, hsw1, hs2, hm2, hsw2⟩ := entry_step2 H0
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
  have hPr := probeOf_csem F ⟨fa.k, af.slotBase⟩ XI
  intro vals cm hrun
  have hR := sim_runG (noncallIndep_pair (noncallIndep_csem F ⟨fa.k, af.slotBase⟩ XI))
    (probeOf_pair hPr) hP Hb Hs hseg htc fuel cs 0 0 kk ρ₁ (w₁, w₁') .refl hmP
  rw [hrun] at hR
  obtain ⟨us, outs, ⟨⟨x1, x2⟩, nc⟩, cm0, sv, hret, -, -, -, -, hmr, -⟩ := hR
  have h1 := vRetFrom_mapW counted_pair_proj₁ hret
  have h2 := vRetFrom_mapW counted_pair_proj₂ hret
  exact ⟨us, outs, x1, x2, nc,
    VRetFrom.prefix (vstar_mapW (counted_probe_proj hPr 0) hs1) h1,
    VRetFrom.prefix (vstar_mapW (counted_probe_proj hPr 0) hs2) h2,
    SameWorld.mono (zof_sub cm0) hmr.2.2⟩

end E2E
