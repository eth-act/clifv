import FV.E2E.FinalTC
import FV.Backend.Proof.DriverCheckTCF
import FV.Backend.Proof.IselNonETF
import FV.Backend.Proof.IselLowerCvtT

/-!
# The typed final theorem with the proven float operations (S11f, #35)

`backend_correct_final[_ex]TC` (`E2E/FinalTC.lean`) for functions whose statements may also be
the S11f float operations whose `lower` roots are proven over float-capable contexts: the
arithmetic, rounding, the saturating/`from` conversions and the scalar comparisons (`fcmp` of
`f32`/`f64`). The scope is `InSubsetTCF` (`InSubsetTC` with `Compile.functionETCF`), the
lowering validator `lowerCheckTCF` (`CompiledTCF`/`CompiledATCF`), the driver simulation
`driver_correctTC` (`LowerSimTC.lean`, whose `DriverHypTC` takes the scope `functionETCF`), and
the driver's statements come from `instCallsTF_of_rules` (the conversion roots
`lowerRulesCorrectCvtT_program`, the `fcmp` roots `lowerRulesCorrectFC_program`, the non-E
unmatchability `nonEUnmatchableTF_program`). The final theorems take no rule-family premise.

* `InSubsetTCF`, `InSubsetTC.toTCF`, `CompiledTCF`, `CompiledATCF`, `CompiledTC.toTCF`,
  `CompiledTCF.toA`;
* `iselSimTCF_of_rules`, `backend_correct_of_rules_exTCF`;
* `backend_correct_m4_exTCF`, `backend_correct_final_exTCF`, `backend_correct_finalTCF`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The CLIF functions the typed theorem with the proven float operations covers**:
`InSubsetTC` with `Compile.functionETCF` (the S11f float arithmetic, rounding and conversions
among the statements). -/
structure InSubsetTCF (p : Clif.Program) (f : Clif.Function) : Prop where
  subsetETCF : Compile.functionETCF f = true
  externCalls : ∀ b ∈ f.blocks, ∀ st ∈ b.body, ∀ fn args, st.inst = .call fn args →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  tryExterns : ∀ b ∈ f.blocks, ∀ fn args et, b.term = .tryCall fn args et →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  abiSigs : sigAbiOk f.sig = true ∧ ∀ e ∈ f.externs, sigAbiOk e.2.sig = true
  indSigs : ∀ s ∈ indSigs f, s.params.length ≤ 8 ∧ sigAbiOk s = true
  storeTyped : Compile.storeTypedB f = true

/-- The scope with typed `try_call`s is in the scope with the float operations. -/
theorem InSubsetTC.toTCF {p : Clif.Program} {f : Clif.Function} (h : InSubsetTC p f) :
    InSubsetTCF p f :=
  ⟨Compile.functionETCF_of_functionETC h.subsetETC, h.externCalls, h.tryExterns, h.abiSigs,
    h.indSigs, h.storeTyped⟩

theorem noTail_of_subsetTCF {p : Clif.Program} {f : Clif.Function} (h : InSubsetTCF p f) :
    ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args := by
  intro B hB fn args ht
  have := h.subsetETCF
  simp only [Compile.functionETCF, Bool.and_eq_true, List.all_eq_true] at this
  have := (this.1.1.2 B hB).2
  rw [ht] at this
  simp [Compile.termE] at this

theorem indSig_of_subsetTCF {p : Clif.Program} {f : Clif.Function} (h : InSubsetTCF p f) :
    ∀ B ∈ f.blocks, ∀ st ∈ B.body, IndSigOk f (indSigs f) st.inst := by
  intro B hB st hst sig callee args s hi hs
  have hmem : s ∈ indSigs f := by
    unfold indSigs
    refine List.mem_flatMap.mpr ⟨B, hB, List.mem_append_left _ (List.mem_filterMap.mpr ⟨st, hst, ?_⟩)⟩
    rw [hi]; exact hs
  exact ⟨hmem, (h.indSigs s hmem).1⟩

theorem tryIndSig_of_subsetTCF {p : Clif.Program} {f : Clif.Function} (h : InSubsetTCF p f) :
    ∀ B ∈ f.blocks, ∀ c args et s, B.term = .tryCallIndirect c args et →
      f.sigDecls.lookup et.sig = some s → s ∈ indSigs f ∧ s.params.length ≤ 8 := by
  intro B hB c args et s ht hs
  have hmem : s ∈ indSigs f := by
    unfold indSigs
    refine List.mem_flatMap.mpr ⟨B, hB, List.mem_append_right _ ?_⟩
    rw [ht]; simp [hs]
  exact ⟨hmem, (h.indSigs s hmem).1⟩

/-- **The compiled code with the float operations** (`CompiledTC` with the validator
`lowerCheckTCF`). -/
structure CompiledTCF (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckTCF f vc = true
  prepare : prepare vc = .ok vcp
  prepOk : prepCheck vc vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `CompiledTCF` with an `AllocChecked` allocation. -/
structure CompiledATCF (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckTCF f vc = true
  prepare : prepare vc = .ok vcp
  prepOk : prepCheck vc vcp = true
  check : AllocChecked vcp rf
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `lowerCheckTC`'s acceptance is `lowerCheckTCF`'s. -/
theorem CompiledTC.toTCF {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledTC f k vc vcp rf af fa fb) :
    CompiledTCF f k vc vcp rf af fa fb :=
  ⟨hc.lower, lowerCheckTCF_of_lowerCheckTC hc.lowerOk, hc.prepare, hc.prepOk, hc.check, hc.alloc,
    hc.emit, hc.layout⟩

theorem CompiledTCF.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledTCF f k vc vcp rf af fa fb) :
    CompiledATCF f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, allocChecked_of_checkAlloc hc.check, hc.alloc,
    hc.emit, hc.layout⟩

/-- **CLIF → VCode for the scope with the float operations, from the rule families**: the
driver hypothesis of `buildCtx`'s context (`loweringTCF_of_check`), the statement calls from the
typed families with the conversion and `fcmp` roots and `NonEUnmatchableTF`
(`instCallsTF_of_rules`), the terminator calls from the typed families, the direct `try_call`s
from the proven `tryRulesCorrectTFP_program` (`tryCallsTC_of_rules`), the `try_call_indirect`s
from the integer typed families. -/
theorem iselSimTCF_of_rules {p : Clif.Program} {f : Clif.Function} {vc : VCode}
    (hsub : InSubsetTCF p f) (hlow : lowerCheckTCF f vc = true)
    (hcfg : ∃ ss ps, vc.cfg = .ok (ss, ps))
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out : Nat} {env : Clif.Env}
    (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hrulesF : LowerRulesCorrectT Isle.Aarch64.program)
    (hrulesA : LowerRulesCorrectFT Isle.Aarch64.program)
    (hrulesC : LowerRulesCorrectCvtT Isle.Aarch64.program)
    (hrulesFC : LowerRulesCorrectFC Isle.Aarch64.program)
    (hnE : NonEUnmatchableTF Isle.Aarch64.program)
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
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringTCF_of_check hlow
  have hctxT : CtxT f ctx :=
    ctxT_of_functionETCF hsub.subsetETCF hshape.hctx.choose_spec hshape.ctxInvT hshape.scope
  have hstT : StoresTyped ctx :=
    storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  intro s'
  refine iselSim_of_driverTC (ctx := ctx) (st0 := st0) (R := R) (gn := gn) (bl := bl) (A := A) ?_
    (hds s') (hmem s') (hFP s')
  exact {
    shape := hshape
    cert := hcert
    dsem := (hds s').toDriverSemG
    insts := instCallsTF_of_rules hrules hrulesF hrulesA hrulesC hrulesFC hnE hcallRules hindRules
      hmemRules hmemF
      (hRef s') (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') (hicalls s') (hmem s')
      (hFP s') (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (callsStack_mono (callsStackTCF_of_check hlow) houtB)
      (memRelOk_holds ⟨F s', syms, slotOff, out⟩ f) hctxT hstT
    terms := termCallsT_of_rules htermRules htermUn hbranch hbranchEx (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) hctxT
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subsetTCF hsub
    subETC := hsub.subsetETCF
    entryLocs := entryOkTCF_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subsetTCF hsub
    tries := ⟨out, tryCallsTC_of_rules (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s') (hFP s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') hshape.ctxInvT,
      tryStack_mono (tryStackTCF_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsT_of_rules htryIndRules htryIndUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hicalls s') hctxT
    tryIndSig := tryIndSig_of_subsetTCF hsub
    cfg := hcfg }

/-- **`backend_correct` for the scope with the float operations, from the rule families**
(`backend_correct_of_rules_exTC` with `InSubsetTCF`, `CompiledATCF`, the conversion and `fcmp`
families and `NonEUnmatchableTF`). -/
theorem backend_correct_of_rules_exTCF {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetTCF p f) (hc : CompiledATCF f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    (hrules : LowerRulesCorrectTI Isle.Aarch64.program)
    (hrulesF : LowerRulesCorrectT Isle.Aarch64.program)
    (hrulesA : LowerRulesCorrectFT Isle.Aarch64.program)
    (hrulesC : LowerRulesCorrectCvtT Isle.Aarch64.program)
    (hrulesFC : LowerRulesCorrectFC Isle.Aarch64.program)
    (hnE : NonEUnmatchableTF Isle.Aarch64.program)
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
    (iselSimTCF_of_rules hsub hc.lowerOk (cfg_of_prepare hc.prepare) hrules hrulesF hrulesA
      hrulesC hrulesFC hnE
      hcallRules hindRules hmemRules hmemF
      htermRules htermUn hbranch hbranchEx htryIndRules htryIndUn hRef hds hcalls
      hicalls hmem hFP houtB)
    (fun s' => prepareCorrect_of_check (hds s') hc.prepOk)
    hM6 hent hres hbe
    (argsAtEntry_bodyT (lowerRFunc_frame hc.alloc) (entryRegsTCF_of_check hc.lowerOk) hbe hargs hargF hres)
    hcs hrel htr fuel

/-- `hasTry_of_hasTryCallAT` for `CompiledATCF`. -/
theorem hasTry_of_hasTryCallATCF {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledATCF f k vc vcp rf af fa fb)
    (h : vcp.hasTryCall = true) : ∃ B ∈ f.blocks, B.term.isTry = true :=
  Classical.byContradiction fun hn => by
    have hf : ∀ B ∈ f.blocks, B.term.isTry = false := fun B hB =>
      Bool.eq_false_iff.mpr fun ht => hn ⟨B, hB, ht⟩
    rw [noTryCall_of_prepCheck hc.prepOk (noTryCallTCF_of_check hc.lowerOk hf)] at h
    cases h

/-- `hasTls_of_vcodeAT` for `CompiledATCF`. -/
theorem hasTls_of_vcodeATCF {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledATCF f k vc vcp rf af fa fb)
    (h : vcp.hasTls = true) : hasTls f = true := by
  cases hf : hasTls f
  · rw [noTls_of_prepCheck hc.prepOk (noTlsTCF_of_check hc.lowerOk hf)] at h
    cases h
  · rfl

theorem outgoing_le_intBaseATCF {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledATCF f k vc vcp rf af fa fb) :
    vc.outgoing ≤ (RAFrame.compute vcp rf).intBase := by
  simp only [RAFrame.compute]
  rw [outgoing_of_prepCheck hc.prepOk]
  exact le_alignTo _ 16 (by decide)

set_option maxHeartbeats 1000000 in
/-- `stackArgsAvoid_frameWAT` for `CompiledATCF`. -/
theorem stackArgsAvoid_frameWATCF {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledATCF f k vc vcp rf af fa fb) {K : Nat}
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

/-- **The typed M4 assembly at `csem` with the float operations** (`backend_correct_m4_exTC`
for `InSubsetTCF`/`CompiledATCF`): every rule family proven (with `lowerRulesCorrectCvtT_program`,
`lowerRulesCorrectFC_program`, `nonEUnmatchableTF_program`), the register-level layer `hM6` as
hypothesis. -/
theorem backend_correct_m4_exTCF {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetTCF p f) (hc : CompiledATCF f k vc vcp rf af fa fb)
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
  backend_correct_of_rules_exTCF hsub hc lowerRulesCorrectTI_program lowerRulesCorrectT_program
    lowerRulesCorrectFT_program lowerRulesCorrectCvtT_program lowerRulesCorrectFC_program
    nonEUnmatchableTF_program hT.callsT hT.indT
    memRulesCorrectRTI_program memRulesCorrectRT_program hT.term hT.termUn hT.branch hT.branchEx
    hT.tryIndT hT.tryIndUn
    hM6 hRef (fun s' => driverSem_csem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_csem (hX s'))
    (fun s' => indCallsRefine_csem (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols)) hmem
    (fun s' => memRefinesFP_csem _ (F s') (ctx s') (X s') (hslotB s')) houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

/-- **The typed final theorem with the float operations, `AllocChecked` allocation**
(`backend_correct_final_exTC` for `InSubsetTCF`/`CompiledATCF`): the Arm run of the compiled
function refines the CLIF run, each returned value in the ABI return register of its class. All
rule families are proven (`typedRules_program`, `tryRulesCorrectTFP_program`, the S11e4/S11f
float families with the conversions and comparisons, the typed integer families); no
`TypedRules` premise. -/
theorem backend_correct_final_exTCF {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetTCF p f) (hc : CompiledATCF f k vc vcp rf af fa fb)
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
  backend_correct_m4_exTCF (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc
    (regLevelCorrect_backend_ex hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallATCF hc h)) (fun h => hTls (hasTls_of_vcodeATCF hc h)))
    (refines_final K vcp rf af fa X) hX hXI (fun _ => hsym)
    (fun _ => memRefines_csem _ _ X hslot hsym) (fun _ => hslot) (outgoing_le_intBaseATCF hc)
    hent hres hbe hargs (stackArgsAvoid_frameWATCF hc hres hent hargs) hcs hrel htr fuel

/-- **The typed final theorem with the proven float operations** (`backend_correct_finalTC`
for `InSubsetTCF`/`CompiledTCF`, the allocation accepted by `checkAlloc`; no rule-family
premise): functions with the S11f float arithmetic (`fadd`…`fmax`, `sqrt`, `fneg`, `fabs`,
`fpromote`, `fdemote`), rounding (`ceil`, `floor`, `trunc`, `nearest`), conversions
(`fcvt_from_{u,s}int`, `fcvt_to_{u,s}int_sat`) and scalar comparisons (`fcmp` of `f32`/`f64`). -/
theorem backend_correct_finalTCF {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetTCF p f) (hc : CompiledTCF f k vc vcp rf af fa fb)
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
  backend_correct_final_exTCF hsub hc.toA hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hargs
    hcs hrel htr fuel

end E2E
