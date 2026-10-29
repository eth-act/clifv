import FV.E2E.TypedRulesProg
import FV.Backend.Proof.LowerSimTC

/-!
# The typed final theorem with typed `try_call`s (S11e6, #419)

`backend_correct_final[_ex]T` (`E2E/FinalT.lean`) for functions whose direct `try_call`s call
callees with `f32`/`f64` parameters and returns: the scope is `InSubsetTC` (`InSubsetT` with
`Compile.functionETC`), the lowering validator `lowerCheckTC` (`CompiledTC`/`CompiledATC`), the
typed driver simulation `driver_correctTC` (`LowerSimTC.lean`), and the driver's direct
`try_call`s come from the proven typed family `tryRulesCorrectTFP_program`
(`tryCallsTC_of_rules`). The other control families are the proven `typedRules_program`, so the
final theorems take no rule-family premise.

* `InSubsetTC`, `InSubsetT.toTC`, `CompiledTC`, `CompiledATC`, `CompiledTC.toA`;
* `iselSim_of_driverTC`, `iselSimTC_of_rules`, `backend_correct_of_rules_exTC`;
* `backend_correct_final_exTC`, `backend_correct_finalTC`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The CLIF functions the typed theorem with typed `try_call`s covers**: `InSubsetT` with
`Compile.functionETC` (a direct `try_call`'s callee may take and return `f32`/`f64`). -/
structure InSubsetTC (p : Clif.Program) (f : Clif.Function) : Prop where
  subsetETC : Compile.functionETC f = true
  externCalls : ∀ b ∈ f.blocks, ∀ st ∈ b.body, ∀ fn args, st.inst = .call fn args →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  tryExterns : ∀ b ∈ f.blocks, ∀ fn args et, b.term = .tryCall fn args et →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  abiSigs : sigAbiOk f.sig = true ∧ ∀ e ∈ f.externs, sigAbiOk e.2.sig = true
  indSigs : ∀ s ∈ indSigs f, s.params.length ≤ 8 ∧ sigAbiOk s = true
  storeTyped : Compile.storeTypedB f = true

/-- The typed scope is in the scope with typed `try_call`s. -/
theorem InSubsetT.toTC {p : Clif.Program} {f : Clif.Function} (h : InSubsetT p f) :
    InSubsetTC p f :=
  ⟨Compile.functionETC_of_functionET h.subsetET, h.externCalls, h.tryExterns, h.abiSigs,
    h.indSigs, h.storeTyped⟩

theorem noTail_of_subsetTC {p : Clif.Program} {f : Clif.Function} (h : InSubsetTC p f) :
    ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args := by
  intro B hB fn args ht
  have := h.subsetETC
  simp only [Compile.functionETC, Bool.and_eq_true, List.all_eq_true] at this
  have := (this.1.1.2 B hB).2
  rw [ht] at this
  simp [Compile.termE] at this

theorem indSig_of_subsetTC {p : Clif.Program} {f : Clif.Function} (h : InSubsetTC p f) :
    ∀ B ∈ f.blocks, ∀ st ∈ B.body, IndSigOk f (indSigs f) st.inst := by
  intro B hB st hst sig callee args s hi hs
  have hmem : s ∈ indSigs f := by
    unfold indSigs
    refine List.mem_flatMap.mpr ⟨B, hB, List.mem_append_left _ (List.mem_filterMap.mpr ⟨st, hst, ?_⟩)⟩
    rw [hi]; exact hs
  exact ⟨hmem, (h.indSigs s hmem).1⟩

theorem tryIndSig_of_subsetTC {p : Clif.Program} {f : Clif.Function} (h : InSubsetTC p f) :
    ∀ B ∈ f.blocks, ∀ c args et s, B.term = .tryCallIndirect c args et →
      f.sigDecls.lookup et.sig = some s → s ∈ indSigs f ∧ s.params.length ≤ 8 := by
  intro B hB c args et s ht hs
  have hmem : s ∈ indSigs f := by
    unfold indSigs
    refine List.mem_flatMap.mpr ⟨B, hB, List.mem_append_right _ ?_⟩
    rw [ht]; simp [hs]
  exact ⟨hmem, (h.indSigs s hmem).1⟩

/-- **The compiled code, typed `try_call`s** (`CompiledT` with the validator `lowerCheckTC`). -/
structure CompiledTC (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckTC f vc = true
  prepare : prepare vc = .ok vcp
  prepOk : prepCheck vc vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `CompiledTC` with an `AllocChecked` allocation. -/
structure CompiledATC (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckTC f vc = true
  prepare : prepare vc = .ok vcp
  prepOk : prepCheck vc vcp = true
  check : AllocChecked vcp rf
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

theorem CompiledTC.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledTC f k vc vcp rf af fa fb) :
    CompiledATC f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, allocChecked_of_checkAlloc hc.check, hc.alloc,
    hc.emit, hc.layout⟩

/-- **CLIF → VCode, typed `try_call`s**, from the typed driver simulation `driver_correctTC`. -/
theorem iselSim_of_driverTC {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHypTC f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p)
    (hds : DriverSem sem) {sb : Nat} (hMem : MemRefines Γ.F sb Γ.syms sem)
    (hFP : MemRefinesFP (fun _ => True) Γ.F sb sem) :
    IselSimT sem Γ env p f vc := by
  intro args cs w₀ ρ₀ hce hrel hargs htr fuel
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
  have hrun := driver_correctTC H hds hMem hFP (mrStable_holds Γ f) hB0 hce.callers hce.func rfl
    hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5, h6⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1 _), h6⟩
  · rw [h] at hrun
    exact hrun

/-- **CLIF → VCode for the scope with typed `try_call`s, from the rule families**: the driver
hypothesis of `buildCtx`'s context (`loweringTC_of_check`), the statement and terminator calls
from the typed families, the direct `try_call`s from the proven `tryRulesCorrectTFP_program`
(`tryCallsTC_of_rules`), the `try_call_indirect`s from the integer typed families. -/
theorem iselSimTC_of_rules {p : Clif.Program} {f : Clif.Function} {vc : VCode}
    (hsub : InSubsetTC p f) (hlow : lowerCheckTC f vc = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps))
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out : Nat} {env : Clif.Env}
    (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hrulesF : LowerRulesCorrectT Isle.Aarch64.program)
    (hrulesA : LowerRulesCorrectFT Isle.Aarch64.program)
    (hnE : NonEUnmatchableT Isle.Aarch64.program)
    (hcallRules : CallRulesCorrectT Isle.Aarch64.program)
    (hindRules : IndRulesCorrectT Isle.Aarch64.program)
    (hmemRules : MemRulesCorrectRTI Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    (htermRules : LowerTermRulesCorrectT Isle.Aarch64.program)
    (htermUn : TermUnmatchableT Isle.Aarch64.program)
    (hbranch : BranchRulesCorrectT Isle.Aarch64.program)
    (hbranchEx : BranchExcludedUnmatchableT Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrectT Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchableT Isle.Aarch64.program)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hFP : ∀ s, MemRefinesFP (fun _ => True) (F s) slotOff (sem s))
    (houtB : vc.outgoing ≤ out) :
    ∀ s, IselSimT (sem s) ⟨F s, syms, slotOff, out⟩ env p f vc := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringTC_of_check hlow
  have hctxT : CtxT f ctx :=
    ctxT_of_functionETCF (Compile.functionETCF_of_functionETC hsub.subsetETC)
      hshape.hctx.choose_spec hshape.ctxInvT hshape.scope
  have hscT : InstScopeT ctx := instScopeT_of_lowerCheckTC hlow hshape.hctx.choose_spec
  have hstT : StoresTyped ctx :=
    storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  intro s'
  refine iselSim_of_driverTC (ctx := ctx) (st0 := st0) (R := R) (gn := gn) (bl := bl) (A := A) ?_
    (hds s') (hmem s') (hFP s')
  exact {
    shape := hshape
    cert := hcert
    dsem := (hds s').toDriverSemG
    insts := instCallsT_of_rules hrules hrulesF hrulesA hnE hcallRules hindRules hmemRules hmemF
      (hRef s') (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') (hicalls s') (hmem s')
      (hFP s') (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (callsStack_mono (callsStackTC_of_check hlow) houtB)
      (memRelOk_holds ⟨F s', syms, slotOff, out⟩ f) hctxT hscT hstT
    terms := termCallsT_of_rules htermRules htermUn hbranch hbranchEx (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) hctxT
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subsetTC hsub
    subETC := Compile.functionETCF_of_functionETC hsub.subsetETC
    entryLocs := entryOkTC_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subsetTC hsub
    tries := ⟨out, tryCallsTC_of_rules (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s') (hFP s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') hshape.ctxInvT,
      tryStack_mono (tryStackTC_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsT_of_rules htryIndRules htryIndUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hicalls s') hctxT
    tryIndSig := tryIndSig_of_subsetTC hsub
    cfg := hcfg }

/-- **`backend_correct` for the scope with typed `try_call`s, from the rule families**
(`backend_correct_of_rules_exT` with `InSubsetTC`, `CompiledATC`; the direct `try_call`s from
the proven typed family). -/
theorem backend_correct_of_rules_exTC {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetTC p f) (hc : CompiledATC f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hrulesF : LowerRulesCorrectT Isle.Aarch64.program)
    (hrulesA : LowerRulesCorrectFT Isle.Aarch64.program)
    (hnE : NonEUnmatchableT Isle.Aarch64.program)
    (hcallRules : CallRulesCorrectT Isle.Aarch64.program)
    (hindRules : IndRulesCorrectT Isle.Aarch64.program)
    (hmemRules : MemRulesCorrectRTI Isle.Aarch64.program)
    (hmemF : MemRulesCorrectRT Isle.Aarch64.program)
    (htermRules : LowerTermRulesCorrectT Isle.Aarch64.program)
    (htermUn : TermUnmatchableT Isle.Aarch64.program)
    (hbranch : BranchRulesCorrectT Isle.Aarch64.program)
    (hbranchEx : BranchExcludedUnmatchableT Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrectT Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchableT Isle.Aarch64.program)
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hFP : ∀ s, MemRefinesFP (fun _ => True) (F s) slotOff (sem s))
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra astep s (Clif.runLoop env p fuel cs) := by
  exact backend_correct_of_layers_exT
    (iselSimTC_of_rules hsub hc.lowerOk (cfg_of_prepare hc.prepare) hrules hrulesF hrulesA hnE
      hcallRules hindRules hmemRules hmemF
      htermRules htermUn hbranch hbranchEx htryIndRules htryIndUn hRef hds hcalls
      hicalls hmem hFP houtB)
    (fun s' => prepareCorrect_of_check (hds s') hc.prepOk)
    hM6 hent hres hbe
    (argsAtEntry_bodyT (lowerRFunc_frame hc.alloc) (entryRegsTC_of_check hc.lowerOk) hbe hargs hargF hres)
    hcs hrel htr fuel

/-- `hasTry_of_hasTryCallAT` for `CompiledATC`. -/
theorem hasTry_of_hasTryCallATC {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledATC f k vc vcp rf af fa fb)
    (h : vcp.hasTryCall = true) : ∃ B ∈ f.blocks, B.term.isTry = true :=
  Classical.byContradiction fun hn => by
    have hf : ∀ B ∈ f.blocks, B.term.isTry = false := fun B hB =>
      Bool.eq_false_iff.mpr fun ht => hn ⟨B, hB, ht⟩
    rw [noTryCall_of_prepCheck hc.prepOk (noTryCallTC_of_check hc.lowerOk hf)] at h
    cases h

/-- `hasTls_of_vcodeAT` for `CompiledATC`. -/
theorem hasTls_of_vcodeATC {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledATC f k vc vcp rf af fa fb)
    (h : vcp.hasTls = true) : hasTls f = true := by
  cases hf : hasTls f
  · rw [noTls_of_prepCheck hc.prepOk (noTlsTC_of_check hc.lowerOk hf)] at h
    cases h
  · rfl

theorem outgoing_le_intBaseATC {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledATC f k vc vcp rf af fa fb) :
    vc.outgoing ≤ (RAFrame.compute vcp rf).intBase := by
  simp only [RAFrame.compute]
  rw [outgoing_of_prepCheck hc.prepOk]
  exact le_alignTo _ 16 (by decide)

set_option maxHeartbeats 1000000 in
/-- `stackArgsAvoid_frameWAT` for `CompiledATC`. -/
theorem stackArgsAvoid_frameWATC {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledATC f k vc vcp rf af fa fb) {K : Nat}
    {s : Arm.ArmState} {base ra : BitVec 64} {args : List Clif.Val} (hres : StackAvail K af s)
    (_hent : AbiEntry fb base ra s) (hargs : ArgsIn f.sig args s) :
    StackArgsAvoid (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
      f.sig args s := by
  intro off v hm j hj hF
  have h := hargs _ _ hm
  simp only at h
  have hframe := lowerRFunc_frame hc.alloc
  have hfs := (lowerRFunc_ok hc.alloc).1.1
  have hD : frameDrop af = af.frameSize + 16 := by simp [frameDrop, hframe]
  have hsz : (RAFrame.compute vcp rf).size ≤ af.frameSize := by
    have e : (RAFrame.compute vcp rf).total =
        alignTo ((RAFrame.compute vcp rf).size + vcp.slotBytes) 16 +
          clobberBytes rf.saved := rfl
    rw [hfs, e]
    exact Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) (le_alignTo16 _))
      (Nat.le_add_right _ _)
  have hsp := hres.1.1
  have hfit := h.fits
  have hx : (spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j -
      (spv s - BitVec.ofNat 64 (frameDrop af))).toNat = off + j + frameDrop af := by
    rw [hD]
    bv_omega
  rcases hF with (⟨-, h2⟩ | ⟨-, h2⟩ | hcode) | ⟨hlt, -⟩
  · rw [hx] at h2; omega
  · rw [hx] at h2; omega
  · have e : spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j = spv s + BitVec.ofNat 64 (off + j) := by
      rw [BitVec.add_assoc]; congr 1
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    rw [e] at hcode
    exact h.noCode j hj hcode
  · rw [(spBody_toNat hres).1] at hlt
    have : (spv s + BitVec.ofNat 64 off + BitVec.ofNat 64 j).toNat = (spv s).toNat + off + j := by
      bv_omega
    omega

/-- **The typed M4 assembly at `csem` with typed `try_call`s** (`backend_correct_m4_exT` for
`InSubsetTC`/`CompiledATC`): every rule family proven, the register-level layer `hM6` as
hypothesis. -/
theorem backend_correct_m4_exTC {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetTC p f) (hc : CompiledATC f k vc vcp rf af fa fb)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hM6 : RegLevelCorrectEx (fun s => csem (F s) (ctx s) (X s)) F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (csem (F s) (ctx s) (X s)))
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hXI : ∀ s, XCallsIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (csem (F s) (ctx s) (X s)))
    (hslotB : ∀ s, (ctx s).slotBase = slotOff)
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra astep s (Clif.runLoop env p fuel cs) :=
  have hT := typedRules_program
  backend_correct_of_rules_exTC hsub hc lowerRulesCorrectTI_program lowerRulesCorrectT_program
    lowerRulesCorrectFT_program nonEUnmatchableT_program hT.callsT hT.indT
    memRulesCorrectRTI_program memRulesCorrectRT_program hT.term hT.termUn hT.branch hT.branchEx
    hT.tryIndT hT.tryIndUn
    hM6 hRef (fun s' => driverSem_csem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_csem (hX s'))
    (fun s' => indCallsRefine_csem (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols)) hmem
    (fun s' => memRefinesFP_csem _ (F s') (ctx s') (X s') (hslotB s')) houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

/-- **The typed final theorem with typed `try_call`s, `AllocChecked` allocation**
(`backend_correct_final_exT` for `InSubsetTC`/`CompiledATC`): the Arm run of the compiled
function refines the CLIF run, each returned value in the ABI return register of its class. All
rule families are proven (`typedRules_program`, `tryRulesCorrectTFP_program`, the S11e4/S11f
float families, the typed integer families); no `TypedRules` premise. -/
theorem backend_correct_final_exTC {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetTC p f) (hc : CompiledATC f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_m4_exTC (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc
    (regLevelCorrect_backend_ex hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallATC hc h)) (fun h => hTls (hasTls_of_vcodeATC hc h)))
    (refines_final K vcp rf af fa X) hX hXI (fun _ => hsym)
    (fun _ => memRefines_csem _ _ X hslot hsym) (fun _ => hslot) (outgoing_le_intBaseATC hc)
    hent hres hbe hargs (stackArgsAvoid_frameWATC hc hres hent hargs) hcs hrel htr fuel

/-- **The typed final theorem with typed `try_call`s** (`backend_correct_finalT` for
`InSubsetTC`/`CompiledTC`, the allocation accepted by `checkAlloc`; no rule-family premise). -/
theorem backend_correct_finalTC {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetTC p f) (hc : CompiledTC f k vc vcp rf af fa fb)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) :=
  backend_correct_final_exTC hsub hc.toA hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hargs
    hcs hrel htr fuel

end E2E
