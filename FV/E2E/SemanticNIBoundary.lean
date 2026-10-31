import FV.E2E.CompiledSemanticNI
import FV.Backend.Proof.SpillCtlPipe

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

namespace CompiledSemanticNI
variable {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
  {af : AFunc} {fa : FnAsm} {fb : FnBin}

theorem check (hc : CompiledSemanticNI f k vc vcp rf af fa fb) : Backend.checkAlloc vcp rf = .ok () :=
  hc.toSemantic.check

theorem alloc (hc : CompiledSemanticNI f k vc vcp rf af fa fb) : lowerRFunc vcp rf = .ok af :=
  hc.toSemantic.alloc

theorem emit (hc : CompiledSemanticNI f k vc vcp rf af fa fb) : emitFunc k af = .ok fa :=
  hc.toSemantic.emit

theorem layout (hc : CompiledSemanticNI f k vc vcp rf af fa fb) : fa.layout = .ok fb :=
  hc.toSemantic.layout

/-- Integer source scope and ABI correctness give the entry locations needed
by whole-program linking; a raw Stock artifact needs no legacy lowerCheck. -/
theorem entryRegs (hc : CompiledSemanticNI f k vc vcp rf af fa fb) :
    ∀ l ∈ locsOf f.sig, ∀ r, l = .reg r → ∃ n, r = .x n ∧ n ≤ 8 := by
  cases hc with
  | compatible h => exact entryRegs_of_check h.lowerOk
  | arithmetic domain equal reads h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int domain.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk domain.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩

  | mixed domain equal reads h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int domain.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk domain.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩

  | logical domain equal reads h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int domain.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk domain.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩

  | scalar domain equal reads h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int domain.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk domain.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩
  | scalarDiv domain equal reads h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int domain.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk domain.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩

  | cfg domain equal reads h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int domain.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk domain.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩

  | memory family equal effects h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int family.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk family.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩

  | memoryCfg family equal effects h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int family.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk family.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩

  | memoryUnsigned family equal effects h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int family.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk family.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩
  | memoryExtending family equal effects h =>
    intro loc member r located
    have regs := (Spill.locsOf_regs (functionE_sig_int family.scope.subsetE).1
      (Spill.sret_le_of_sigAbiOk family.abi)).2
    have found : r ∈ Spill.locRegs (locsOf f.sig) :=
      List.mem_filterMap.mpr ⟨loc,member,by rw [located]⟩
    obtain ⟨n,bound,pin⟩ := regs r found
    exact ⟨n,pin,bound⟩

/-- An ABI-read-only artifact contains no TLS helper; cleanup and checked
preparation preserve that exclusion. -/
theorem noTls {sig : Clif.Signature} {code : VCode}
    (checked : Backend.ABIReadOnly.check sig code = true) : code.hasTls = false := by
  rw [VCode.hasTls,Array.any_eq_false']
  intro vb member
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i member'
  obtain ⟨b,hb⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member)
  obtain ⟨k,hi⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member')
  have supported := ABIReadOnly.checked_instruction checked (by simpa using hb) (by simpa using hi)
  cases i <;> simp_all [Backend.ABIReadOnly.instruction,Backend.DeadCleanup.pureNoFlags,Backend.DeadCleanup.pureForm]

theorem noTlsFlags {sig : Clif.Signature} {code : VCode}
    (checked : Backend.ABIReadFlags.check sig code = true) : code.hasTls = false := by
  rw [VCode.hasTls,Array.any_eq_false']
  intro vb member
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i member'
  obtain ⟨b,hb⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member)
  obtain ⟨k,hi⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member')
  have supported := MixedFlagBoundary.checked_instruction checked (by simpa using hb) (by simpa using hi)
  cases i <;> simp_all [Backend.ABIReadOnly.instruction,Backend.DeadCleanup.pureNoFlags,Backend.DeadCleanup.pureForm,Backend.ABIReadFlags.extra]

/-- Scalar producers add no TLS read; the retained ABI checks keep their exclusions. -/
theorem noTlsScalar {sig : Clif.Signature} {code : VCode}
    (checked : Backend.ABIReadScalar.check sig code = true) : code.hasTls = false := by
  rw [VCode.hasTls,Array.any_eq_false']
  intro vb member
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i member'
  obtain ⟨b,hb⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member)
  obtain ⟨k,hi⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member')
  have supported := ScalarBoundary.checked_instruction checked (by simpa using hb) (by simpa using hi)
  cases i <;> simp_all [Backend.ABIReadScalar.instruction,Backend.ABIReadScalar.constant,Backend.ABIReadScalar.shift,Backend.ABIReadScalar.extension,Backend.ABIReadScalar.bitProducer,Backend.ABIReadScalar.popcountProducer,Backend.ABIReadScalar.comparisonProducer,Backend.ABIReadScalar.booleanProducer,Backend.ABIReadScalar.highmulProducer,Backend.ABIReadScalar.extendedComparisonProducer,Backend.ABIReadScalar.maskProducer,
    Backend.ABIReadFlags.instruction,Backend.ABIReadOnly.instruction,
    Backend.DeadCleanup.pureNoFlags,Backend.DeadCleanup.pureForm,Backend.ABIReadFlags.extra]
/-- Scalar producers add no TLS read; the retained ABI checks keep their exclusions. -/
theorem noTlsDiv {sig : Clif.Signature} {code : VCode}
    (checked : Backend.ABIReadDiv.check sig code = true) : code.hasTls = false := by
  rw [VCode.hasTls,Array.any_eq_false']
  intro vb member
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i member'
  obtain ⟨b,hb⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member)
  obtain ⟨k,hi⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member')
  have supported := DivBoundary.checked_instruction checked (by simpa using hb) (by simpa using hi)
  cases i <;> simp_all [Backend.ABIReadDiv.instruction,Backend.ABIReadDiv.additional,Backend.ABIReadScalar.instruction,Backend.ABIReadScalar.constant,Backend.ABIReadScalar.shift,Backend.ABIReadScalar.extension,Backend.ABIReadScalar.bitProducer,Backend.ABIReadScalar.popcountProducer,Backend.ABIReadScalar.comparisonProducer,Backend.ABIReadScalar.booleanProducer,Backend.ABIReadScalar.highmulProducer,Backend.ABIReadScalar.extendedComparisonProducer,Backend.ABIReadScalar.maskProducer,
    Backend.ABIReadFlags.instruction,Backend.ABIReadOnly.instruction,
    Backend.DeadCleanup.pureNoFlags,Backend.DeadCleanup.pureForm,Backend.ABIReadFlags.extra]

theorem noTlsCfg {sig : Clif.Signature} {code : VCode}
    (checked : Backend.ABIReadCfg.check sig code = true) : code.hasTls = false := by
  rw [VCode.hasTls,Array.any_eq_false']
  intro vb member
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i member'
  obtain ⟨b,hb⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member)
  obtain ⟨k,hi⟩ := List.mem_iff_getElem?.mp (Array.mem_toList_iff.mpr member')
  have supported := CfgBoundary.checked_instruction checked (by simpa using hb) (by simpa using hi)
  cases i <;> simp_all [Backend.ABIReadCfg.instruction,Backend.ABIReadCfg.additional,Backend.ABIReadDiv.instruction,Backend.ABIReadDiv.additional,Backend.ABIReadScalar.instruction,Backend.ABIReadScalar.constant,Backend.ABIReadScalar.shift,Backend.ABIReadScalar.extension,Backend.ABIReadScalar.bitProducer,Backend.ABIReadScalar.popcountProducer,Backend.ABIReadScalar.comparisonProducer,Backend.ABIReadScalar.booleanProducer,Backend.ABIReadScalar.highmulProducer,Backend.ABIReadScalar.extendedComparisonProducer,Backend.ABIReadScalar.maskProducer,
    Backend.ABIReadFlags.instruction,Backend.ABIReadOnly.instruction,
    Backend.DeadCleanup.pureNoFlags,Backend.DeadCleanup.pureForm,Backend.ABIReadFlags.extra]

end CompiledSemanticNI

/-- The existing whole-program TLS contract also applies to paired semantic
artifacts; the new pure arithmetic route has no TLS instructions. -/
theorem hasTls_of_vcode_semantic {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hc : CompiledSemanticNI f k vc vcp rf af fa fb) (ht : vcp.hasTls = true) : hasTls f = true := by
  cases hc with
  | compatible h => exact hasTls_of_vcode_production h ht
  | @arithmetic cleanup result domain equal reads h =>
    have raw := CompiledSemanticNI.noTls reads
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht

  | @mixed cleanup result domain equal reads h =>
    have raw := CompiledSemanticNI.noTlsFlags reads
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht

  | @logical cleanup result domain equal reads h =>
    have raw := CompiledSemanticNI.noTlsFlags reads
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht

  | @scalar cleanup result domain equal reads h =>
    have raw := CompiledSemanticNI.noTlsScalar reads
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht
  | @scalarDiv cleanup result domain equal reads h =>
    have raw := CompiledSemanticNI.noTlsDiv reads
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht

  | @cfg cleanup result domain equal reads h =>
    have raw := CompiledSemanticNI.noTlsCfg reads
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht

  | @memory cleanup result family equal effects h =>
    have raw := Stock.Memory.effectsOnly_noTls effects
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht

  | @memoryCfg cleanup result family equal effects h =>
    have raw := Stock.MemoryCfg.effectsOnly_noTls effects
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht

  | @memoryUnsigned width cleanup result family equal effects h =>
    have raw := Stock.Memory.effectsOnly_noTls effects
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht
  | @memoryExtending kind ty cleanup result family equal effects h =>
    have raw := Stock.Memory.effectsOnly_noTls effects
    have staged : (Stock.Arithmetic.stage cleanup result.code).hasTls = false := by
      rw [equal]
      cases cleanup with
      | false => exact raw
      | true => exact Backend.DeadCleanup.prune_noTls raw
    have prepared := noTls_of_prepCheck h.prepOk staged
    rw [prepared] at ht
    cases ht

set_option maxHeartbeats 1000000 in
/-- Stack-argument avoidance follows from actual physical allocation and the
original hardware ABI entry; lowering provenance is irrelevant to the bound. -/
theorem stackArgsAvoid_frameW_semantic {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledSemanticNI f k vc vcp rf af fa fb) {K : Nat}
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
  have hsp := hres.1
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


theorem backend_correct_world_semantic {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledSemanticNI f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    (∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
    (∀ c', Clif.runLoop env p fuel cs = .trapped c' →
      ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
        ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
        ∃ n, TrapAt fb base c' (runX (ArmStepX X H fa) n s)) := by
  have both := backend_correct_worldX_semantic (K := K) hsub hc.toSemantic hcov hX hXI hsym hslot hcs hrel hargs htr fuel
  refine ⟨fun vals cm returned => ?_,fun code trapped H G base ra s entry => ?_⟩
  · obtain ⟨us,outs,w,pins,arity,values,memory,site,run⟩ := both.1 vals cm returned
    refine ⟨us,outs,w,pins,arity,values,memory,site,?_⟩
    intro H G base ra s entry
    obtain ⟨n,ret,trace,_⟩ := run H G base ra s entry
    exact ⟨n,ret,trace⟩
  · obtain ⟨n,trap,_⟩ := both.2 code trapped H G base ra s entry
    exact ⟨n,trap⟩

theorem backend_correct_world_ni_semantic {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledSemanticNI f k vc vcp rf af fa fb)
    {X : ExtSem} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env} {K : Nat}
    {F : BitVec 64 → Prop} {c : BitVec 64}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hX : XCallsOk env (f.externs.map (·.2))
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hXI : XCallsIndOk env (indSigs f)
      (RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hcs : ClifEntry f args cs)
    (hrel : RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀)
    (hargs : ArgsAtEntry F f.sig args w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ∀ vals cm, Clif.runLoop env p fuel cs = .returned vals cm →
      ∃ (us : List (Reg × Reg)) (outs : List CV) (w : Arm.ArmState),
        us.map (·.2) = (List.range us.length).map Reg.x ∧ us.length = outs.length ∧
        PrefixHold vals outs ∧ MemRel F syms cm w ∧ vc.RetsSite us ∧
        (∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
          ActEntry vcp rf af fa fb K F G X H base ra s w₀ →
          ∃ n, ActRet ra F G us outs w s (runX (ArmStepX X H fa) n s) ∧
            PostTrace fa af base (ArmStepX X H fa) s n) ∧
        (XNI F syms (f.externs.map (·.2)) (indSigs f) c
          (CallLg env (f.externs.map (·.2)) (indSigs f)) X → XTls F X →
        ∀ (D : BitVec 64 → Prop) (w₀' : Arm.ArmState),
          RelW ⟨F, syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f c cs.frame.slots cs.mem w₀' →
          SameWorld (fun b => F b ∨ D b) w₀ w₀' →
          (∀ r v, (ArgLoc.reg r, v) ∈ (locsOf f.sig).zip args → regVal w₀' r = regVal w₀ r) →
          (∀ off v, (ArgLoc.stack off, v) ∈ (locsOf f.sig).zip args → ∀ k < v.ty.bytes,
            w₀'.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k) =
              w₀.mem (Arm.r (.GPR 29#5) w₀ + BitVec.ofInt 64 (16 + (off : Int)) + BitVec.ofNat 64 k)) →
          ∀ (H : ArmHooks) (G : BitVec 64 → Prop) (base ra : BitVec 64) (s : Arm.ArmState),
            ActEntry vcp rf af fa fb K F G X H base ra s w₀' →
            ∃ n, ActRet ra (fun a => F a ∨ D a) G us outs w s (runX (ArmStepX X H fa) n s) ∧
              PostTrace fa af base (ArmStepX X H fa) s n) := by
  intro vals cm returned
  obtain ⟨us,outs,w,pins,arity,values,memory,site,run,paired⟩ :=
    backend_correct_world_niX_semantic (K := K) hsub hc hcov hX hXI hsym hslot hcs hrel hargs htr fuel vals cm returned
  refine ⟨us,outs,w,pins,arity,values,memory,site,?_,?_⟩
  · intro H G base ra s entry
    obtain ⟨n,ret,trace,_⟩ := run H G base ra s entry
    exact ⟨n,ret,trace⟩
  · intro hNI hTls D w' rel worlds regs stack H G base ra s entry
    obtain ⟨n,ret,trace,_⟩ := paired hNI hTls D w' rel worlds regs stack H G base ra s entry
    exact ⟨n,ret,trace⟩

end E2E
