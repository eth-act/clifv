import FV.E2E.PairDriverDValue
import FV.E2E.PairDriverID
import FV.E2E.BackendPairRunD
import FV.E2E.BackendWorldCleanupI
import FV.E2E.DeadCleanupGot

/-!
# The guarded paired run of the cleanup path (SEM1 #537, #713, cleanup path)

`vcode_niID` and `backend_pairRunD` (`PairDriverID.lean`, `BackendPairRunD.lean`) for the shipped
compiler's cleanup path (`CompiledCleanup`): the paired counted run of the selected code in the
guarded paired value semantics `pairDI (valueSem F ctx) F ctx XI` (the paired contracts of
`PairDriverDValue.lean`, the entry by `entry_step2PDG`), carried to the allocated code through the
cleanup stage: the skip of unused instructions (`skipStage f vc`, the kept-code simulation
`sim_runGK` from the entry `entry_step2PDGZ`) and the dead-code cleanup (`prune_correctW` on the
paired semantics: a pure form keeps both worlds,
`pairDI_value_pure`; a compare writes only the flags of both worlds and the forms that follow it
up to the next compare read no memory, so the pair guard holds trivially there,
`cmpOverwrite_pairSemD_value`), `prepare` (`prep_soundW`) and the GOT guard
(`vRetFrom_gotVPDV`). The per-step lockstep of the two runs is `StepLockV` (`XNI` or `XNIF` with
the world difference inside `F`):

* `valueSem_at_noncall`, `ncIndep_pairD_value`, `probeOf_pairD_value`, `noCallProj_pairD_value`;
* `vcode_niID_valueL`, **`vcode_niID_value`** (`XNI`), **`vcode_niIDF_value`** (`XNIF`, `D ⊆ F`);
* **`vcode_niID_valueL_stage`**: `vcode_niID_valueL` for `skipStage f vc`;
* `pairDI_value_pure`, `cmpOverwrite_countedW`, `cmpOverwrite_pairSemD_value`,
  `valueSemV_of_some`, `gotInvPDV_step`, `gotInvPDV_star`, `vRetFrom_gotVPDV`;
* `backend_pairRunD_cleanupL`, **`backend_pairRunD_cleanup`** (`XNI`),
  **`backend_pairRunDF_cleanup`** (`XNIF`, `D ⊆ F`): the paired run of `vcp` in
  `pairDI (valueSemV (GotV vcp) F ctx) F ctx XI`, the input of the value two-run chain
  (`backend_twoRunLWNpV`, …, `backend_twoRunLERWZIUV`).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- `valueSem` of a non-call is the same at every call index. -/
theorem valueSem_at_noncall (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSemI) {i : MInst}
    (h : i.isCallI = false) (n n' : Nat) :
    valueSem F ctx (X.at n) i = valueSem F ctx (X.at n') i := by
  funext us w
  simp only [valueSem, csem_at_noncall F ctx X h n n']

/-- The guarded paired value family: the non-calls do not read the call number. -/
theorem ncIndep_pairD_value (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) :
    NcIndep (fun n => pairSemD (valueSem F ctx (XI.at n)) F ctx (XI.at n)) := by
  intro m n i h
  exact pairSemD_congr (valueSem_at_noncall F ctx XI h m n) fun Y => csem_at_noncall Y ctx XI h m n

/-- The guarded paired value probes (calls failing) are probes of the guarded paired value
family. -/
theorem probeOf_pairD_value (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) :
    ProbeOf (fun n => pairSemD (valueSem F ctx (XI.at n).noCall) F ctx (XI.at n).noCall)
      (fun n => pairSemD (valueSem F ctx (XI.at n)) F ctx (XI.at n)) where
  noncall n i hc := by
    have he : ∀ Y, csem Y ctx (XI.at n).noCall i = csem Y ctx (XI.at n) i := fun Y =>
      csem_call_congr Y ctx (XI.at n) _ hc
    have hv : valueSem F ctx (XI.at n).noCall i = valueSem F ctx (XI.at n) i := by
      funext us w
      simp only [valueSem, he F]
    exact pairSemD_congr hv he
  call n i hc uses w := by
    show pairSemD (valueSem F ctx (XI.at n).noCall) F ctx (XI.at n).noCall i uses w = none
    cases h : pairSemD (valueSem F ctx (XI.at n).noCall) F ctx (XI.at n).noCall i uses w with
    | none => rfl
    | some r =>
      obtain ⟨outs, w', ctl⟩ := r
      have h' := (pairSemD_sub h).2
      simp [pairSem, valueSem, specForm_of_isCallI hc, csem_noCall_call hc] at h'

/-- The guarded paired value probes (calls failing) project into the counted guarded semantics. -/
theorem noCallProj_pairD_value (F : BitVec 64 → Prop) (ctx : FnCtx) (XI : ExtSemI) :
    NoCallProj (fun n => pairSemD (valueSem F ctx (XI.at n)) F ctx (XI.at n))
      (fun n => pairSemD (valueSem F ctx (XI.at n).noCall) F ctx (XI.at n).noCall) :=
  fun n => counted_probe_proj (probeOf_pairD_value F ctx XI) n

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- **Non-interference of the counted VCode run of the cleanup path, reads guarded**, for any
per-step lockstep of the two guarded value runs (`StepLockV`). -/
theorem vcode_niID_valueL (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    {D : BitVec 64 → Prop}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hLS : ∀ s n, ReachN env p cs s n →
      StepLockV F D syms (XI.at n) (env.only (Clif.Invoked env p s)) f c)
    (hTls : ∀ n, XTls F (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ w₀' : Arm.ArmState}
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
            pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) F ⟨fa.k, af.slotBase⟩ (XI.at n))
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 := by
  intro vals cm hrun
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have houtB := outgoing_le_intBaseCleanupA hc.toA
  have Hb1 : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW_cleanup hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _)
      (xCallsIndOk_none _ _ _ _) hsym hslot
  have Hs1 : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW_cleanup hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2
      hsym hslot
  have mkP : ∀ {X : ExtSem} {env' : Clif.Env},
      DriverHyp f vc ctx st0 R gn bl A (valueSem F ⟨fa.k, af.slotBase⟩ X) (RelW Γ f c) env' p →
      XCallsOk env' (f.externs.map (·.2)) (RelW Γ f c) X →
      XCallsIndOk env' (indSigs f) (RelW Γ f c) X →
      (∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) →
      StepLockV F D syms X env' f c → XTls F X →
      DriverHyp f vc ctx st0 R gn bl A
        (pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ X) F ⟨fa.k, af.slotBase⟩ X) (MRP Γ f c D)
        env' p :=
    fun H hX' hXI' hsym' hLS' hTls' => {
      shape := hshape
      cert := hcert
      dsem := driverSemG_pairD_value F ⟨fa.k, af.slotBase⟩ _
      insts := instCalls_pairD_value hc hX' hXI' hsym' hslot hLS'
      terms := termCalls_pairD_value Γ rfl hTls' ⟨fa.k, af.slotBase⟩
      ext := H.ext
      indSig := H.indSig
      subE := H.subE
      entryLocs := H.entryLocs
      brIdx := H.brIdx
      noTail := H.noTail
      tries := ⟨_, tryCalls_pairD_value hc hX' hsym' hslot hLS',
        tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
      tryExt := H.tryExt
      tryInd := tryIndCalls_pairD_value hXI' hsym' hLS'
      tryIndSig := H.tryIndSig
      cfg := H.cfg }
  have HbP : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall) F ⟨fa.k, af.slotBase⟩
        (XI.at n).noCall)
      (MRP Γ f c D) (env.only fun _ _ _ => False) p := fun n =>
    mkP (Hb1 n) (xCallsOk_none _ _ _ _) (xCallsIndOk_none _ _ _ _) hsym
      (stepLockV_of_xni (xNI_noCall _) (hTls n)) (hTls n)
  have HsP : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (MRP Γ f c D) (env.only (Clif.Invoked env p s)) p := fun s n hr =>
    mkP (Hs1 s n hr) (hX s n hr).1 (hX s n hr).2 hsym (hLS s n hr) (hTls n)
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
  obtain ⟨kk, ρ₁, w₁, w₁', -, hm1, hsw1, -, hm2, hsw2, hsP⟩ := entry_step2PDG (Hb1 0)
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_valueSem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c)
    (ctx' := ⟨fa.k, af.slotBase⟩) (X := (XI.at 0).noCall) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmP : Match f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ := by
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w₁ w₁' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  have hR := sim_runIG (ncIndep_pairD_value F ⟨fa.k, af.slotBase⟩ XI)
    (noCallProj_pairD_value F ⟨fa.k, af.slotBase⟩ XI) hP HbP HsP hseg htc fuel cs 0 0 kk ρ₁
    (w₁, w₁') .refl hmP
  rw [hrun] at hR
  obtain ⟨us, outs, w, cm0, -, hret, -, -, -, -, hmr, -⟩ := hR
  exact ⟨us, outs, w, VRetFrom.prefix (vstar_mapW
    (noCallProj_pairD_value F ⟨fa.k, af.slotBase⟩ XI 0) hsP) hret,
    SameWorld.mono (zof_sub cm0) hmr.2.2⟩

/-- **`vcode_niID_valueL` for the code after the skip of unused instructions** (`skipStage f vc`,
which the cleanup stage prunes and prepares): the paired entry in the entry code
(`entry_step2PDGZ`, kept whole, `entry_runK`), then the counted paired run of the kept code
(`sim_runGK`, the guarded paired value family with its probes, `probeOf_pairD_value`). -/
theorem vcode_niID_valueL_stage (hsub : InSubset p f)
    (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    {D : BitVec 64 → Prop}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hLS : ∀ s n, ReachN env p cs s n →
      StepLockV F D syms (XI.at n) (env.only (Clif.Invoked env p s)) f c)
    (hTls : ∀ n, XTls F (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ w₀' : Arm.ArmState}
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
        VRetFrom (skipStage f vc) (ISem.counted fun n =>
            pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) F ⟨fa.k, af.slotBase⟩ (XI.at n))
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
  rcases hsk with heq | hK
  · rw [heq]
    exact vcode_niID_valueL hsub hc hone htc hX hLS hTls hsym hslot ρ₀ hce hrel hrel' hargs hsw
      hreg hstk htr fuel
  intro vals cm hrun
  let Γ : Rel := ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  have houtB := outgoing_le_intBaseCleanupA hc.toA
  have Hb1 : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall)
      (RelW Γ f c) (env.only fun _ _ _ => False) p := fun n =>
    driverHyp_relW_cleanup hsub hc hshape hcert hbr (xCallsOk_none _ _ _ _)
      (xCallsIndOk_none _ _ _ _) hsym hslot
  have Hs1 : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) (RelW Γ f c) (env.only (Clif.Invoked env p s)) p :=
    fun s n hr => driverHyp_relW_cleanup hsub hc hshape hcert hbr (hX s n hr).1 (hX s n hr).2
      hsym hslot
  have mkP : ∀ {X : ExtSem} {env' : Clif.Env},
      DriverHyp f vc ctx st0 R gn bl A (valueSem F ⟨fa.k, af.slotBase⟩ X) (RelW Γ f c) env' p →
      XCallsOk env' (f.externs.map (·.2)) (RelW Γ f c) X →
      XCallsIndOk env' (indSigs f) (RelW Γ f c) X →
      (∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b) →
      StepLockV F D syms X env' f c → XTls F X →
      DriverHyp f vc ctx st0 R gn bl A
        (pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ X) F ⟨fa.k, af.slotBase⟩ X) (MRP Γ f c D)
        env' p :=
    fun H hX' hXI' hsym' hLS' hTls' => {
      shape := hshape
      cert := hcert
      dsem := driverSemG_pairD_value F ⟨fa.k, af.slotBase⟩ _
      insts := instCalls_pairD_value hc hX' hXI' hsym' hslot hLS'
      terms := termCalls_pairD_value Γ rfl hTls' ⟨fa.k, af.slotBase⟩
      ext := H.ext
      indSig := H.indSig
      subE := H.subE
      entryLocs := H.entryLocs
      brIdx := H.brIdx
      noTail := H.noTail
      tries := ⟨_, tryCalls_pairD_value hc hX' hsym' hslot hLS',
        tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
      tryExt := H.tryExt
      tryInd := tryIndCalls_pairD_value hXI' hsym' hLS'
      tryIndSig := H.tryIndSig
      cfg := H.cfg }
  have HbP : ∀ n, DriverHyp f vc ctx st0 R gn bl A
      (pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n).noCall) F ⟨fa.k, af.slotBase⟩
        (XI.at n).noCall)
      (MRP Γ f c D) (env.only fun _ _ _ => False) p := fun n =>
    mkP (Hb1 n) (xCallsOk_none _ _ _ _) (xCallsIndOk_none _ _ _ _) hsym
      (stepLockV_of_xni (xNI_noCall _) (hTls n)) (hTls n)
  have HsP : ∀ s n, ReachN env p cs s n → DriverHyp f vc ctx st0 R gn bl A
      (pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) F ⟨fa.k, af.slotBase⟩ (XI.at n))
      (MRP Γ f c D) (env.only (Clif.Invoked env p s)) p := fun s n hr =>
    mkP (Hs1 s n hr) (hX s n hr).1 (hX s n hr).2 hsym (hLS s n hr) (hTls n)
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
  obtain ⟨kk, ρ₁, w₁, w₁', -, hm1, hsw1, -, hm2, hsw2, hsP⟩ := entry_step2PDGZ (Hb1 0)
    (driverSem_valueSem F ⟨fa.k, af.slotBase⟩ (XI.at 0).noCall)
    (memRefines_valueSem _ _ (XI.at 0).noCall hslot hsym) (mrStable_relW Γ f c)
    (ctx' := ⟨fa.k, af.slotBase⟩) (X := (XI.at 0).noCall) hB0 hce.callers
    hce.func rfl hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hrel' hargs hreg h29 hstk
  have hFD : ∀ a, F a → F a ∨ D a := fun a h => .inl h
  have hmP : Match f ctx R gn bl A (MRP Γ f c D) cs.frame.slots cs ⟨0, kk, ρ₁, (w₁, w₁')⟩ := by
    refine ⟨hm1.1, hm1.2.1, hm1.2.2.1, ⟨hm1.2.2.2.1, hm2.2.2.2.1, ?_⟩, hm1.2.2.2.2⟩
    have h01 : SameWorld (fun b => F b ∨ D b) w₁ w₁' :=
      SameWorld.trans (SameWorld.mono hFD hsw1)
        (SameWorld.trans hsw (SameWorld.symm (SameWorld.mono hFD hsw2)))
    exact sameWorld_zof hm1.2.2.2.1.1.1 hm2.2.2.2.1.1.1 h01 (fun b h => h)
  have hPrP := probeOf_pairD_value F ⟨fa.k, af.slotBase⟩ XI
  have hsK := entry_runK hK hB0 (entry_pos hB0 hbody hm1) hsP
  have hR := sim_runGK hK
    (fun i h m m' => ncIndep_pairD_value F ⟨fa.k, af.slotBase⟩ XI m m' i h) hPrP hP HbP HsP hseg
    htc fuel cs 0 0 (kidx (skipMask f R bl vc (skipAt f (skipDrops f R bl vc)) 0) kk) ρ₁
    (w₁, w₁') .refl ⟨⟨0, kk, ρ₁, (w₁, w₁')⟩, ⟨rfl, rfl, rfl, fun _ _ => rfl⟩, hmP⟩
  rw [hrun] at hR
  obtain ⟨us, outs, w, cm0, -, hret, -, -, -, -, hmr, -⟩ := hR
  exact ⟨us, outs, w, VRetFrom.prefix (vstar_mapW (counted_probe_proj hPrP 0) hsK) hret,
    SameWorld.mono (zof_sub cm0) hmr.2.2⟩

/-- **Non-interference of the counted VCode run of the cleanup path, reads guarded**
(`vcode_niID` for `CompiledCleanup`). -/
theorem vcode_niID_value (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
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
            pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) F ⟨fa.k, af.slotBase⟩ (XI.at n))
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 :=
  vcode_niID_valueL hsub hc hone htc hX (fun s n hr => stepLockV_of_xni (hNI s n hr) (hTls n)) hTls
    hsym hslot ρ₀ hce hrel hrel' hargs hsw hreg hstk htr fuel

/-- **Non-interference of the counted VCode run of the cleanup path, from `XNIF`**
(`vcode_niIDF` for `CompiledCleanup`: the external semantics non-interfering at `F` only, the
world difference inside `F`). -/
theorem vcode_niIDF_value (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
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
      ∃ us outs w,
        VRetFrom vc (ISem.counted fun n =>
            pairSemD (valueSem F ⟨fa.k, af.slotBase⟩ (XI.at n)) F ⟨fa.k, af.slotBase⟩ (XI.at n))
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 :=
  vcode_niID_valueL hsub hc hone htc hX
    (fun s n hr => stepLockV_of_xnif (hNI s n hr) hD (hTls n)) hTls hsym hslot ρ₀ hce hrel hrel'
    hargs hsw hreg hstk htr fuel

end

/-! ## Through the cleanup, `prepare` and the GOT guard -/

section
variable {F : BitVec 64 → Prop} {ctx : FnCtx} {XI : ExtSemI}

/-- A pure form keeps both worlds of the guarded paired value semantics. -/
theorem pairDI_value_pure {i : MInst} {us : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    {outs : List CV} {w' : (Arm.ArmState × Arm.ArmState) × Nat} {ctl : Ctl}
    (hi : pureForm i = true) (h : pairDI (valueSem F ctx) F ctx XI i us w = some (outs, w', ctl)) :
    w' = w ∧ ctl = .next := by
  obtain ⟨h1, h2⟩ := ISem.counted_some h
  obtain ⟨-, hp⟩ := pairSemD_sub h1
  obtain ⟨g1, g2⟩ := pairSem_inv hp
  obtain ⟨e1, e2⟩ := valueSem_pure hi g1
  obtain ⟨e1', -⟩ := valueSem_pure hi g2
  rw [pureForm_isCallI hi] at h2
  exact ⟨Prod.ext (Prod.ext e1 e1') h2, e2⟩

/-- **The counted semantics lets a compare's flags be overwritten** when every member does (any
world type; `cmpOverwrite_counted` is the `Sem` instance). -/
theorem cmpOverwrite_countedW {W : Type} {sem : Nat → ISem CV W} (h : ∀ n, CmpOverwrite (sem n)) :
    CmpOverwrite (ISem.counted sem) := by
  refine ⟨fun i us w outs w' ctl hi hs => ?_, fun l us w outs w' ctl hs => ?_⟩
  · obtain ⟨h1, h2⟩ := ISem.counted_some hs
    simp only [cmpForm_isCallI hi, Bool.false_eq_true, ↓reduceIte] at h2 h1
    obtain ⟨hc, hK, hJ⟩ := (h w.2).1 _ _ _ _ _ _ hi h1
    obtain ⟨wa, na⟩ := w
    obtain ⟨wb, nb⟩ := w'
    simp only at h1 h2 hK hJ
    subst h2
    refine ⟨hc, fun K us' r hK' hs' => ?_, fun j us' outs' ctl' hj hs' => ?_⟩
    · simp only [ISem.counted, Option.map_eq_some_iff] at hs' ⊢
      obtain ⟨r', hr', e⟩ := hs'
      exact ⟨r', hK K us' r' hK' hr', e⟩
    · obtain ⟨g1, g2⟩ := ISem.counted_some hs'
      simp only at g1 g2
      have hnc : j.isCallI = false := by
        cases hjc : j.isCallI with
        | false => rfl
        | true => rw [hjc] at g2; simp at g2
      have := hJ j us' outs' ctl' hj g1
      simp only [ISem.counted, this, Option.map_some, hnc, Bool.false_eq_true, ↓reduceIte]
  · obtain ⟨h1, h2⟩ := ISem.counted_some hs
    obtain ⟨e1, j, e2⟩ := (h w.2).2 _ _ _ _ _ _ h1
    refine ⟨Prod.ext e1 ?_, j, e2⟩
    rw [h2]; rfl

/-- A flag-free form or a `jump` is no load form. -/
theorem loadForm_of_flagFree_or_jump {j : MInst} (hj : (flagFree j || isJump j) = true) :
    j.loadForm = false := by
  rcases Bool.or_eq_true_iff.mp hj with h | h
  · exact specForm_loadForm (specForm_of_pure (pureForm_of_flagFree h))
  · cases j <;> first | rfl | (simp [isJump] at h)

/-- **The guarded paired value semantics lets a compare's flags be overwritten**: a compare, the
flag-free forms and `jump` read no memory, so the pair guard holds there and the paired steps are
the two value steps (`valueSem_cmpOverwrite` on each world). -/
theorem cmpOverwrite_pairSemD_value (F : BitVec 64 → Prop) (ctx : FnCtx) (X : ExtSem) :
    CmpOverwrite (pairSemD (valueSem F ctx X) F ctx X) := by
  have hc := valueSem_cmpOverwrite F ctx X
  refine ⟨fun i us w outs w' ctl hi hs => ?_, fun l us w outs w' ctl hs => ?_⟩
  · obtain ⟨-, hs⟩ := pairSemD_sub hs
    obtain ⟨h1, h2⟩ := pairSem_inv hs
    obtain ⟨hc1, hK1, hJ1⟩ := hc.1 _ _ _ _ _ _ hi h1
    obtain ⟨-, hK2, hJ2⟩ := hc.1 _ _ _ _ _ _ hi h2
    refine ⟨hc1, fun K us' r hK hs' => ?_, fun j us' outs' ctl' hj hs' => ?_⟩
    · have hKl : K.loadForm = false := specForm_loadForm (by simp [specForm, hK])
      rw [pairSemD_of (pGuard_noLoad hKl _ _)] at hs' ⊢
      obtain ⟨o, q, c⟩ := r
      obtain ⟨g1, g2⟩ := pairSem_inv hs'
      exact pairSem_eq (hK1 K us' _ hK g1) (hK2 K us' _ hK g2)
    · have hjl := loadForm_of_flagFree_or_jump hj
      rw [pairSemD_of (pGuard_noLoad hjl _ _)] at hs' ⊢
      obtain ⟨g1, g2⟩ := pairSem_inv hs'
      exact pairSem_eq (hJ1 j us' outs' ctl' hj g1) (hJ2 j us' outs' ctl' hj g2)
  · obtain ⟨-, hs⟩ := pairSemD_sub hs
    obtain ⟨h1, h2⟩ := pairSem_inv hs
    obtain ⟨e1, j, e2⟩ := hc.2 _ _ _ _ _ _ h1
    obtain ⟨e1', -, -⟩ := hc.2 _ _ _ _ _ _ h2
    exact ⟨Prod.ext e1 e1', j, e2⟩

/-- **`valueSemV` defined at one world is `valueSem` at every world** (its GOT guard reads only
the use values; `csemV_of_some`). -/
theorem valueSemV_of_some {gv : Nat → String → Prop} {X : ExtSem} {i : MInst} {us : List CV}
    {w : Arm.ArmState} {r : List CV × Arm.ArmState × Ctl}
    (h : valueSemV gv F ctx X i us w = some r) (w' : Arm.ArmState) :
    valueSemV gv F ctx X i us w' = valueSem F ctx X i us w' := by
  by_cases hp : specForm i = true
  · simp only [valueSemV, valueSem, hp, ↓reduceIte]
  · have hc : csemV gv F ctx X i us w = some r := by simpa [valueSemV, hp] using h
    simp only [valueSemV, valueSem, hp, Bool.false_eq_true, ↓reduceIte]
    exact csemV_of_some hc w'

variable {vc : VCode}

/-- **One counted guarded paired value step** keeps the GOT invariant and is a step of the guarded
paired `valueSemV (GotV vc)`. -/
theorem gotInvPDV_step {s : VState CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    {c' : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)} (hI : GotInvP vc XI s)
    (h : VStep vc (pairDI (valueSem F ctx) F ctx XI) (.run s) c') :
    VStep vc (pairDI (valueSemV (GotV vc) F ctx) F ctx XI) (.run s) c' ∧
      ∀ s', c' = .run s' → GotInvP vc XI s' := by
  obtain ⟨b, k, ρ, ⟨⟨w, w'⟩, m⟩⟩ := s
  cases h with
  | @step _ _ _ _ vb i ops outs w₂ ctl _ hvb hi hops hsem hlen hnext =>
  obtain ⟨hs, -⟩ := ISem.counted_some hsem
  obtain ⟨hg, hsP⟩ := pairSemD_sub hs
  obtain ⟨hs1, -⟩ := pairSem_inv hsP
  dsimp only at hg hs1
  have hg' : PGuard F ctx (XI.at m) i (vuses ops ρ) (w, w') := hg
  let π : (Arm.ArmState × Arm.ArmState) × Nat → Arm.ArmState := fun p => p.1.1
  have hst1 : VStep vc (valueSem F ctx (XI.at m)) (.run ⟨b, k, ρ, w⟩) (c'.mapW π) :=
    VStep.step hvb hi hops hs1 hlen (VNext_mapW (π := π) hnext)
  have hI' : GotInv vc (XI.at m) ⟨b, k, ρ, w⟩ := hI
  obtain ⟨hst2, hinv⟩ := gotInv_step_value hI' hst1
  have hV : ∀ x, valueSemV (GotV vc) F ctx (XI.at m) i (vuses ops ρ) x =
      valueSem F ctx (XI.at m) i (vuses ops ρ) x := by
    cases hst2 with
    | step hvb2 hi2 hops2 hsem2 _ _ =>
      rw [hvb] at hvb2; cases hvb2
      rw [hi] at hi2; cases hi2
      rw [hops] at hops2; cases hops2
      exact valueSemV_of_some hsem2
  refine ⟨VStep.step hvb hi hops ?_ hlen hnext, fun s' hc => ?_⟩
  · have e : pairSemD (valueSemV (GotV vc) F ctx (XI.at m)) F ctx (XI.at m) i (vuses ops ρ)
        (w, w') = pairSemD (valueSem F ctx (XI.at m)) F ctx (XI.at m) i (vuses ops ρ) (w, w') := by
      rw [pairSemD_of hg', pairSemD_of hg']
      simp only [pairSem, hV]
    show (pairSemD (valueSemV (GotV vc) F ctx (XI.at m)) F ctx (XI.at m) i (vuses ops ρ)
      (w, w')).map _ = _
    rw [e]
    exact hsem
  · subst hc
    exact hinv _ rfl

theorem gotInvPDV_star {s s' : VState CV ((Arm.ArmState × Arm.ArmState) × Nat)}
    (hI : GotInvP vc XI s)
    (h : Star (VStep vc (pairDI (valueSem F ctx) F ctx XI)) (.run s) (.run s')) :
    Star (VStep vc (pairDI (valueSemV (GotV vc) F ctx) F ctx XI)) (.run s) (.run s') ∧
      GotInvP vc XI s' := by
  generalize ha : (VConf.run s : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)) = a at h
  generalize hb : (VConf.run s' : VConf CV ((Arm.ArmState × Arm.ArmState) × Nat)) = b at h
  induction h generalizing s with
  | refl => subst ha; cases hb; exact ⟨.refl _, hI⟩
  | @step a1 a2 a3 h1 h2 ih =>
    subst ha
    cases a2 with
    | run s2 =>
      obtain ⟨h1', hI2⟩ := gotInvPDV_step hI h1
      obtain ⟨h2', hI'⟩ := ih (hI2 s2 rfl) rfl hb
      exact ⟨.step h1' h2', hI'⟩
    | ret vals w => subst hb; cases h2 with | step h _ => cases h
    | halt w => subst hb; cases h2 with | step h _ => cases h

/-- **A returning counted guarded paired value run is one of `valueSemV (GotV vc)`.** -/
theorem vRetFrom_gotVPDV {ρ₀ : Nat → CV} {w₀ : (Arm.ArmState × Arm.ArmState) × Nat}
    {us : List (Reg × Reg)} {vals : List CV} {w : (Arm.ArmState × Arm.ArmState) × Nat}
    (h : VRetFrom vc (pairDI (valueSem F ctx) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ us vals w) :
    VRetFrom vc (pairDI (valueSemV (GotV vc) F ctx) F ctx XI) ⟨0, 0, ρ₀, w₀⟩ us vals w := by
  obtain ⟨b, k, ρ, w₁, vb, ops, outs, hs, hvb, hk, hops, hvals, hsem⟩ := h
  obtain ⟨hs', -⟩ := gotInvPDV_star
    (show GotInvP vc XI ⟨0, 0, ρ₀, w₀⟩ from gotInv_entry vc (XI.at 0) ρ₀ w₀.1.1) hs
  refine ⟨b, k, ρ, w₁, vb, ops, outs, hs', hvb, hk, hops, hvals, ?_⟩
  have hnc : ∀ info, ((MInst.rets us) = .call info ∨ ∃ ti, (MInst.rets us) = .tryCall info ti) →
      gotGuard (GotV vc) (XI.at w₁.2) info vals := fun info h => by
    rcases h with h | ⟨_, h⟩ <;> cases h
  have e : pairSemD (valueSemV (GotV vc) F ctx (XI.at w₁.2)) F ctx (XI.at w₁.2) (.rets us) vals
      w₁.1 = pairSemD (valueSem F ctx (XI.at w₁.2)) F ctx (XI.at w₁.2) (.rets us) vals w₁.1 := by
    rw [pairSemD_of (pGuard_noLoad rfl _ _), pairSemD_of (pGuard_noLoad rfl _ _)]
    simp only [pairSem, valueSemV, valueSem, specForm, pureForm, cmpForm, Bool.false_or,
      Bool.false_eq_true, ↓reduceIte, csemV_eq hnc]
  show (pairSemD (valueSemV (GotV vc) F ctx (XI.at w₁.2)) F ctx (XI.at w₁.2) (.rets us) vals
    w₁.1).map _ = _
  rw [e]
  exact hsem

end

section
variable {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

/-- **The paired run of the allocated code of the cleanup path, reads guarded**, for any per-step
lockstep of the two guarded value runs (`StepLockV`). -/
theorem backend_pairRunD_cleanupL (hsub : InSubset p f)
    (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hone : InstCallsOne f) (htc : TryCallsOne f)
    {XI : ExtSemI} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {F : BitVec 64 → Prop} {c : BitVec 64} {args : List Clif.Val} {cs : Clif.State}
    {D : BitVec 64 → Prop}
    (hX : ∀ s n, ReachN env p cs s n →
      XCallsOk (env.only (Clif.Invoked env p s)) (f.externs.map (·.2))
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n) ∧
      XCallsIndOk (env.only (Clif.Invoked env p s)) (indSigs f)
        (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) (XI.at n))
    (hLS : ∀ s n, ReachN env p cs s n →
      StepLockV F D syms (XI.at n) (env.only (Clif.Invoked env p s)) f c)
    (hTls : ∀ n, XTls F (XI.at n))
    (hsym : ∀ n b, syms n = some b → XI.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ w₀' : Arm.ArmState} (ρ₀ : Nat → CV) (hce : ClifEntry f args cs)
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
        VRetFrom vcp (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 := by
  intro vals cm hrun
  obtain ⟨us, outs, w, hv, hsw'⟩ := vcode_niID_valueL_stage hsub hc hone htc hX hLS hTls hsym
    hslot ρ₀ hce hrel hrel' hargs hsw hreg hstk htr fuel vals cm hrun
  have hPr := (prune_correctW (vc := skipStage f vc)
    (sem := pairDI (valueSem F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
    (fun _ _ _ _ _ _ hi hs => pairDI_value_pure hi hs)
    (cmpOverwrite_countedW fun n => cmpOverwrite_pairSemD_value _ _ _) ρ₀ ((w₀, w₀'), 0)).1 _ _ _ hv
  have hP := (prep_soundW (DriverSemG.countedW fun n =>
    driverSemG_pairD_value F ⟨fa.k, af.slotBase⟩ (XI.at n)) hc.prepOk ρ₀ ((w₀, w₀'), 0)).1 _ _ _ hPr
  exact ⟨us, outs, w, vRetFrom_gotVPDV hP, hsw'⟩

/-- **The paired run of the allocated code of the cleanup path, reads guarded by the difference
set** (`backend_pairRunD` for `CompiledCleanup`). -/
theorem backend_pairRunD_cleanup (hsub : InSubset p f)
    (hc : CompiledCleanup f k vc vcp rf af fa fb)
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
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ us outs w,
        VRetFrom vcp (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 :=
  backend_pairRunD_cleanupL hsub hc hone htc hX
    (fun s n hr => stepLockV_of_xni (hNI s n hr) (hTls n)) hTls hsym hslot ρ₀ hce hrel hrel' hargs
    hsw hreg hstk htr fuel

/-- **The paired run of the allocated code of the cleanup path from `XNIF`** (`backend_pairRunDF`
for `CompiledCleanup`: the external semantics non-interfering at `F` only, the world difference
inside `F`). -/
theorem backend_pairRunDF_cleanup (hsub : InSubset p f)
    (hc : CompiledCleanup f k vc vcp rf af fa fb)
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
      ∃ us outs w,
        VRetFrom vcp (pairDI (valueSemV (GotV vcp) F ⟨fa.k, af.slotBase⟩) F ⟨fa.k, af.slotBase⟩ XI)
          ⟨0, 0, ρ₀, ((w₀, w₀'), 0)⟩ us outs w ∧
        SameWorld (fun b => F b ∨ D b) w.1.1 w.1.2 :=
  backend_pairRunD_cleanupL hsub hc hone htc hX
    (fun s n hr => stepLockV_of_xnif (hNI s n hr) hD (hTls n)) hTls hsym hslot ρ₀ hce hrel hrel'
    hargs hsw hreg hstk htr fuel

end

end E2E
