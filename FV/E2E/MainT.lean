import FV.E2E.Main
import FV.E2E.ComposeT

/-!
# Typed `backend_correct` (S11e5 Stage C, slice 7)

`Main.lean`'s theorems for the typed movement scope (`Compile.functionET`: `f32`/`f64` values in
data movement, function signatures and block parameters; integer calls):

* `InSubsetT` (`InSubset` with `functionET`), `CompiledT`/`CompiledAT` (`Compiled`/`CompiledA`
  with the typed lowering validator `lowerCheckT`), `LoweringObligationsT`
  (`loweringObligationsT_of_check`, from `loweringT_of_check`);
* `iselSim_of_driverT` (from `driver_correctT`; the stack-passed float parameters are loaded
  under `MemRefinesFP`), `argsAtEntry_bodyT` (register arguments in x0–x8 or v0–v7);
* `backend_correct_of_rules_exT` / `backend_correct_of_rulesT`: the typed rule families
  (`LowerContractT.lean`) give `ArmRefinesT`.

Integer specializations: `InSubset.toT`, `Compiled.toT`, `CompiledA.toT`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The CLIF functions the typed theorem covers**: `InSubset` with the typed movement scope
`Compile.functionET` in place of subset E (the other conditions unchanged), and the CLIF
verifier's typing of float stores (`Compile.storeTypedB`: a float `store` stores a float-defined
value; `storeTypedB_of_functionE` for subset E). -/
structure InSubsetT (p : Clif.Program) (f : Clif.Function) : Prop where
  subsetET : Compile.functionET f = true
  externCalls : ∀ b ∈ f.blocks, ∀ st ∈ b.body, ∀ fn args, st.inst = .call fn args →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  tryExterns : ∀ b ∈ f.blocks, ∀ fn args et, b.term = .tryCall fn args et →
    ∀ e, f.extern? fn = some e → p.func? e.name = none
  abiSigs : sigAbiOk f.sig = true ∧ ∀ e ∈ f.externs, sigAbiOk e.2.sig = true
  /-- the signatures of the indirect calls pass `sigAbiOk` (`InSubset.indSigs`; before S5 they
  also had at most 8 parameters) -/
  indSigs : ∀ s ∈ indSigs f, sigAbiOk s = true
  storeTyped : Compile.storeTypedB f = true

/-- **Integer specialization**: the subset is in the typed one. -/
theorem InSubset.toT {p : Clif.Program} {f : Clif.Function} (h : InSubset p f) : InSubsetT p f :=
  ⟨Compile.functionET_of_functionE h.subsetE, h.externCalls, h.tryExterns, h.abiSigs, h.indSigs,
    Compile.storeTypedB_of_functionE h.subsetE⟩

theorem noTail_of_subsetT {p : Clif.Program} {f : Clif.Function} (h : InSubsetT p f) :
    ∀ B ∈ f.blocks, ∀ fn args, B.term ≠ .returnCall fn args := by
  intro B hB fn args ht
  have := h.subsetET
  simp only [Compile.functionET, Bool.and_eq_true, List.all_eq_true] at this
  have := (this.1.1.2 B hB).2
  rw [ht] at this
  simp [Compile.termE] at this

theorem indSig_of_subsetT {p : Clif.Program} {f : Clif.Function} (h : InSubsetT p f) :
    ∀ B ∈ f.blocks, ∀ st ∈ B.body, IndSigOk f (indSigs f) st.inst := by
  intro B hB st hst sig callee args s hi hs
  have hmem : s ∈ indSigs f := by
    unfold indSigs
    refine List.mem_flatMap.mpr ⟨B, hB, List.mem_append_left _ (List.mem_filterMap.mpr ⟨st, hst, ?_⟩)⟩
    rw [hi]; exact hs
  exact hmem

theorem tryIndSig_of_subsetT {p : Clif.Program} {f : Clif.Function} (h : InSubsetT p f) :
    ∀ B ∈ f.blocks, ∀ c args et s, B.term = .tryCallIndirect c args et →
      f.sigDecls.lookup et.sig = some s → s ∈ indSigs f := by
  intro B hB c args et s ht hs
  have hmem : s ∈ indSigs f := by
    unfold indSigs
    refine List.mem_flatMap.mpr ⟨B, hB, List.mem_append_right _ ?_⟩
    rw [ht]; simp [hs]
  exact hmem

/-- **The compiled code, typed** (`Compiled` with the typed lowering validator `lowerCheckT`). -/
structure CompiledT (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckT f vc = true
  prepare : prepare vc = .ok vcp
  prepOk : prepCheck vc vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `CompiledT` with an `AllocChecked` allocation (`CompiledA` with `lowerCheckT`). -/
structure CompiledAT (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheckT f vc = true
  prepare : prepare vc = .ok vcp
  prepOk : prepCheck vc vcp = true
  check : AllocChecked vcp rf
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

theorem CompiledT.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledT f k vc vcp rf af fa fb) :
    CompiledAT f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, allocChecked_of_checkAlloc hc.check, hc.alloc,
    hc.emit, hc.layout⟩

/-- **Integer specialization**: the integer validator's acceptance is the typed one's. -/
theorem Compiled.toT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : Compiled f k vc vcp rf af fa fb) :
    CompiledT f k vc vcp rf af fa fb :=
  ⟨hc.lower, lowerCheckT_of_lowerCheck hc.lowerOk, hc.prepare, hc.prepOk, hc.check, hc.alloc,
    hc.emit, hc.layout⟩

theorem CompiledA.toT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledA f k vc vcp rf af fa fb) :
    CompiledAT f k vc vcp rf af fa fb :=
  ⟨hc.lower, lowerCheckT_of_lowerCheck hc.lowerOk, hc.prepare, hc.prepOk, hc.check, hc.alloc,
    hc.emit, hc.layout⟩

/-- **The typed lowering obligations**: the typed structure of the VCode (`LowerShapeT`), an SSA
availability certificate and the `br_table` index typing. -/
def LoweringObligationsT (f : Clif.Function) (vc : VCode) : Prop :=
  ∃ ctx st0 R gn bl A, LowerShapeT f vc ctx st0 R gn bl ∧ Cert f ctx st0 gn bl A ∧
    ∀ B ∈ f.blocks, BrIdxTyped ctx B.term

/-- **The typed lowering obligations** from the typed lowering validator. -/
theorem loweringObligationsT_of_check {f : Clif.Function} {vc : VCode}
    (h : lowerCheckT f vc = true) : LoweringObligationsT f vc :=
  loweringT_of_check h

/-- **CLIF → VCode, typed**, from the typed driver simulation (the entry loads read memory
through `sem`'s load forms: `MemRefines`, `MemRefinesFP`). -/
theorem iselSim_of_driverT {f : Clif.Function} {vc : VCode} {ctx : Ctx} {st0 : LState}
    {R : Reg → Reg} {gn : Nat → Nat} {bl : List BLow} {A : Nat → Nat → List Clif.ValueId}
    {sem : Sem} {Γ : Rel} {env : Clif.Env} {p : Clif.Program}
    (H : DriverHypT f vc ctx st0 R gn bl A sem (fun sl cm w => Γ.holds f sl cm w) env p)
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
  have hrun := driver_correctT H hds hMem hFP (mrStable_holds Γ f) hB0 hce.callers hce.func rfl
    hbody hterm hregs hty.symm hce.sig (ρ₀ := ρ₀) hrel hargs hP fuel
  refine ⟨fun vals cm h => ?_, fun c h => ?_⟩
  · rw [h] at hrun
    obtain ⟨us, outs, w, cm0, hret, h1, h2, h3, h4, h5, h6⟩ := hrun
    exact ⟨us, outs, w, hret, h1, h2, h3, h5 ▸ memRel_leave (memRel_free h4.1 _), h6⟩
  · rw [h] at hrun
    exact hrun

/-- The arguments of the ABI entry state `s` are where the typed entry code reads them in the
body-entry world `w₀`: the register-passed ones in x0–x8 or v0–v7 (kept by the prologue,
`BodyEntry.args`/`argsV`), the stack-passed ones at `fp + 16 + off`. -/
theorem argsAtEntry_bodyT {f : Clif.Function} {args : List Clif.Val} {af : AFunc}
    {s w₀ : Arm.ArmState} {F : BitVec 64 → Prop} (hframe : af.frame = true)
    (hregs : ∀ l ∈ locsOf f.sig, ∀ r, l = .reg r →
      (∃ n, r = .x n ∧ n ≤ 8) ∨ (∃ n, r = .v n ∧ n ≤ 7))
    (hbe : BodyEntry af s w₀) (h : ArgsIn f.sig args s) (hav : StackArgsAvoid F f.sig args s) :
    ArgsAtEntry F f.sig args w₀ := by
  intro loc v hm
  have hl : loc ∈ locsOf f.sig := (List.of_mem_zip hm).1
  have h1 := h loc v hm
  have hfp : Arm.r (.GPR 29#5) w₀ = spv s - 16#64 := by
    have := hbe.fp; simp only [hframe, ↓reduceIte] at this; exact this
  cases loc with
  | reg r =>
    simp only at h1 ⊢
    rcases hregs _ hl r rfl with ⟨n, rfl, hn⟩ | ⟨n, rfl, hn⟩
    · rw [regVal_x, show xreg n w₀ = xreg n s from hbe.args n (by omega)]
      exact h1
    · rw [show regVal w₀ (.v n) = regVal s (.v n) from hbe.argsV n (by omega)]
      exact h1
  | stack off =>
    simp only at h1 ⊢
    rw [hfp, fp_off_eq]
    refine ⟨hav off v hm, ?_⟩
    rw [show Arm.read_mem_bytes v.ty.bytes (spv s + BitVec.ofNat 64 off) w₀ =
        Arm.read_mem_bytes v.ty.bytes (spv s + BitVec.ofNat 64 off) s from
      read_mem_bytes_congr _ _ (fun k _ => by rw [hbe.mem])]
    exact h1.bytes

/-- **CLIF → VCode for the typed scope, from the typed rule families**: the typed driver
hypothesis of the context `buildCtx` builds (`loweringObligationsT_of_check`, `CtxT` from the
typed shape and `functionET`; its float stores store float values, `storesTyped_of_buildCtx`),
with the driver's calls from the typed rule families
(`instCallsT_of_rules`, `termCallsT_of_rules`, `tryCallsT_of_rules`, `tryIndCallsT_of_rules`). -/
theorem iselSimT_of_rules {p : Clif.Program} {f : Clif.Function} {vc : VCode}
    (hsub : InSubsetT p f) (hlow : lowerCheckT f vc = true)
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
    (htryRules : TryRulesCorrectT Isle.Aarch64.program)
    (htryUn : TryUnmatchableT Isle.Aarch64.program)
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
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligationsT_of_check hlow
  have hctxT : CtxT f ctx := CtxT.ofExterns hshape.ctxInvT hshape.scope (functionET_externs hsub.subsetET)
  have hstT : StoresTyped ctx :=
    storesTyped_of_buildCtx hsub.storeTyped hshape.hctx.choose_spec
  intro s'
  refine iselSim_of_driverT (ctx := ctx) (st0 := st0) (R := R) (gn := gn) (bl := bl) (A := A) ?_
    (hds s') (hmem s') (hFP s')
  exact {
    shape := hshape
    cert := hcert
    dsem := (hds s').toDriverSemG
    insts := instCallsT_of_rules hrules hrulesF hrulesA hnE hcallRules hindRules hmemRules hmemF
      (hRef s') (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') (hicalls s') (hmem s')
      (hFP s') (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (callsStack_mono (callsStackT_of_check hlow) houtB)
      (indStack_mono (indStackT_of_check hlow) houtB)
      (memRelOk_holds ⟨F s', syms, slotOff, out⟩ f) hctxT hshape.scope hstT
    terms := termCallsT_of_rules htermRules htermUn hbranch hbranchEx (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) hctxT
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subsetT hsub
    subET := hsub.subsetET
    entryLocs := entryOkT_of_check hlow
    brIdx := hbr
    noTail := noTail_of_subsetT hsub
    tries := ⟨out, tryCallsT_of_rules htryRules htryUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') hctxT,
      tryStack_mono (tryStackT_of_check hlow) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := tryIndCallsT_of_rules htryIndRules htryIndUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (indStack_mono (indStackT_of_check hlow) houtB) (hicalls s') hctxT
    tryIndSig := tryIndSig_of_subsetT hsub
    cfg := hcfg }

/-- **`backend_correct` for the typed scope, from the typed rule families** (`CompiledAT`,
`RegLevelCorrectEx`): the Arm run refines the CLIF run, each returned value in the ABI return
register of its class (`ArmRefinesT`). Hypotheses: the typed M4 families over float-capable
contexts (FloatsC7F: `LowerRulesCorrectTI`, `NonEUnmatchableT`, `CallRulesCorrectT`,
`IndRulesCorrectT`, `MemRulesCorrectRTI`, the terminator/branch/`try_call` families and their
unmatchability; S11e4/S11f's float families `LowerRulesCorrectT`, `LowerRulesCorrectFT`,
`MemRulesCorrectRT`), M6+M5 (`hM6`), the shared semantics facts, and the float accesses'
`MemRefinesFP`. -/
theorem backend_correct_of_rules_exT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledAT f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M4 over float-capable contexts
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
    (htryRules : TryRulesCorrectT Isle.Aarch64.program)
    (htryUn : TryUnmatchableT Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrectT Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchableT Isle.Aarch64.program)
    -- M6 + M5
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    -- the shared VCode semantics
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    -- the float loads/stores (`ldr`/`str` of `s`/`d` registers)
    (hFP : ∀ s, MemRefinesFP (fun _ => True) (F s) slotOff (sem s))
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesT fb base ra astep s (Clif.runLoop env p fuel cs) := by
  exact backend_correct_of_layers_exT
    (iselSimT_of_rules hsub hc.lowerOk (cfg_of_prepare hc.prepare) hrules hrulesF hrulesA hnE
      hcallRules hindRules hmemRules hmemF
      htermRules htermUn hbranch hbranchEx htryRules htryUn htryIndRules htryIndUn hRef hds hcalls
      hicalls hmem hFP houtB)
    (fun s' => prepareCorrect_of_check (hds s') hc.prepOk)
    hM6 hent hres hbe
    (argsAtEntry_bodyT (lowerRFunc_frame hc.alloc) (entryRegsT_of_check hc.lowerOk) hbe hargs hargF)
    hcs hrel htr fuel

/-- **Integer returns** (`backend_correct_of_rules_exT` for a function whose returns are
integers): the conclusion is `ArmRefines`. -/
theorem backend_correct_of_rules_ex_ofT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledAT f k vc vcp rf af fa fb)
    (hint : f.sig.returns.all (·.ty.isInt) = true)
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
    (htryRules : TryRulesCorrectT Isle.Aarch64.program)
    (htryUn : TryUnmatchableT Isle.Aarch64.program)
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
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_layers_ex_ofT hint
    (iselSimT_of_rules hsub hc.lowerOk (cfg_of_prepare hc.prepare) hrules hrulesF hrulesA hnE
      hcallRules hindRules hmemRules hmemF
      htermRules htermUn hbranch hbranchEx htryRules htryUn htryIndRules htryIndUn hRef hds hcalls
      hicalls hmem hFP houtB)
    (fun s' => prepareCorrect_of_check (hds s') hc.prepOk)
    hM6 hent hres hbe
    (argsAtEntry_bodyT (lowerRFunc_frame hc.alloc) (entryRegsT_of_check hc.lowerOk) hbe hargs hargF)
    hcs hrel htr fuel

/-- **`backend_correct` for the typed scope** (`CompiledT`, `RegLevelCorrect`). -/
theorem backend_correct_of_rulesT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb)
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
    (htryRules : TryRulesCorrectT Isle.Aarch64.program)
    (htryUn : TryUnmatchableT Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrectT Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchableT Isle.Aarch64.program)
    (hM6 : RegLevelCorrect sem F K astep vcp af fb)
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
    ArmRefinesT fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_rules_exT hsub hc.toA hrules hrulesF hrulesA hnE hcallRules hindRules
    hmemRules hmemF htermRules htermUn hbranch hbranchEx htryRules htryUn htryIndRules htryIndUn
    hM6.ex hRef hds hcalls hicalls hmem hFP houtB hent hres hbe hargs hargF hcs hrel htr fuel

end E2E
