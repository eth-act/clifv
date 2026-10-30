import FV.E2E.Final
import FV.E2E.MainT
import FV.E2E.GuardedFP
import FV.Backend.Proof.IselFloatMem
import FV.Backend.Proof.IselLowerAllTI
import FV.Backend.Proof.IselMemAllTI
import FV.Backend.Proof.IselNonETI
import FV.Backend.Proof.LowerContractTP

/-! # The typed final theorem (S11e5 Stage C, slice 7)

`backend_correct_final[_ex]` for the typed movement scope (`InSubsetT`, `CompiledT`/
`CompiledAT`): the VCode semantics is M6's concrete `csem`, whose scalar FP loads/stores satisfy
`MemRefinesFP` (`memRefinesFP_csem`); S11e4/S11f's float families are the proven
`lowerRulesCorrectT_program`, `lowerRulesCorrectFT_program`, `memRulesCorrectRT_program`, the
integer `lower`/memory roots over typed contexts the proven `lowerRulesCorrectTI_program`,
`memRulesCorrectRTI_program`, `nonEUnmatchableT_program` (FloatsC7F; the last under the store
typing `InSubsetT.storeTyped`); the control families over float-capable contexts are the premise
`TypedRules` (FloatsC5: call, terminator, branch and `try_call` roots). The register-level layer is
`regLevelCorrect_backend[_ex]` (allocation-generic; the allocation premise is `CompiledAT.check`,
`lowerRFunc`'s control-form check is `CompiledAT.alloc`).

* `backend_correct_m4_exT`, `backend_correct_final_exT`, `backend_correct_finalT`:
  `ArmRefinesT` (each returned value in its class's return register).
* Integer specialization: `backend_correct_final_ofT` — `backend_correct_final`'s premises and
  conclusion (`ArmRefines`), through the typed chain (`InSubset.toT`, `Compiled.toT`, integer
  returns `backend_correct_of_rules_ex_ofT`), given `TypedRules`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver

/-- **The M4 families over float-capable contexts that are not yet proven**: the control roots
(calls, terminators, branches, `try_call`; `LowerContractT.lean`), the call families with pinned
calls (`LowerContractTP.lean`: the unpinned ones follow, `TypedRules.callsT` …; the pinned ones
are the per-step contracts of the two-world driver). The hypotheses of the typed final, world
and link theorems. -/
structure TypedRules : Prop where
  calls : CallRulesCorrectTP Isle.Aarch64.program
  ind : IndRulesCorrectTP Isle.Aarch64.program
  term : LowerTermRulesCorrectT Isle.Aarch64.program
  termUn : TermUnmatchableT Isle.Aarch64.program
  branch : BranchRulesCorrectT Isle.Aarch64.program
  branchEx : BranchExcludedUnmatchableT Isle.Aarch64.program
  try_ : TryRulesCorrectTP Isle.Aarch64.program
  tryUn : TryUnmatchableT Isle.Aarch64.program
  tryInd : TryIndRulesCorrectTP Isle.Aarch64.program
  tryIndUn : TryIndUnmatchableT Isle.Aarch64.program

theorem TypedRules.callsT (h : TypedRules) : CallRulesCorrectT Isle.Aarch64.program :=
  callRulesCorrectT_of_P h.calls

theorem TypedRules.indT (h : TypedRules) : IndRulesCorrectT Isle.Aarch64.program :=
  indRulesCorrectT_of_P h.ind

theorem TypedRules.tryT (h : TypedRules) : TryRulesCorrectT Isle.Aarch64.program :=
  tryRulesCorrectT_of_P h.try_

theorem TypedRules.tryIndT (h : TypedRules) : TryIndRulesCorrectT Isle.Aarch64.program :=
  tryIndRulesCorrectT_of_P h.tryInd

/-- `hasTry_of_hasTryCallA` for `CompiledAT`. -/
theorem hasTry_of_hasTryCallAT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledAT f k vc vcp rf af fa fb)
    (h : vcp.hasTryCall = true) : ∃ B ∈ f.blocks, B.term.isTry = true :=
  Classical.byContradiction fun hn => by
    have hf : ∀ B ∈ f.blocks, B.term.isTry = false := fun B hB =>
      Bool.eq_false_iff.mpr fun ht => hn ⟨B, hB, ht⟩
    rw [noTryCall_of_prepCheck hc.prepOk (noTryCallT_of_check hc.lowerOk hf)] at h
    cases h

/-- `hasTls_of_vcodeA` for `CompiledAT`. -/
theorem hasTls_of_vcodeAT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledAT f k vc vcp rf af fa fb)
    (h : vcp.hasTls = true) : hasTls f = true := by
  cases hf : hasTls f
  · rw [noTls_of_prepCheck hc.prepOk (noTlsT_of_check hc.lowerOk hf)] at h
    cases h
  · rfl

/-- `outgoing_le_intBaseA` for `CompiledAT`. -/
theorem outgoing_le_intBaseAT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledAT f k vc vcp rf af fa fb) :
    vc.outgoing ≤ (RAFrame.compute vcp rf).intBase := by
  simp only [RAFrame.compute]
  rw [outgoing_of_prepCheck hc.prepOk]
  exact le_alignTo _ 16 (by decide)

set_option maxHeartbeats 1000000 in
/-- `stackArgsAvoid_frameWA` for `CompiledAT`. -/
theorem stackArgsAvoid_frameWAT {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hc : CompiledAT f k vc vcp rf af fa fb) {K : Nat}
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

/-- **The typed M4 assembly at `csem`** (`backend_correct_m4_ex` for the typed scope): the float
families proven, `DriverSem`/`CallsRefine`/`IndCallsRefine`/`MemRefinesFP` from `csem`; the
other typed families (`TypedRules`) and the register-level layer (`hM6`) as hypotheses. -/
theorem backend_correct_m4_exT {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledAT f k vc vcp rf af fa fb) (hT : TypedRules)
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
  backend_correct_of_rules_exT hsub hc lowerRulesCorrectTI_program lowerRulesCorrectT_program
    lowerRulesCorrectFT_program nonEUnmatchableT_program hT.callsT hT.indT
    memRulesCorrectRTI_program
    memRulesCorrectRT_program hT.term
    hT.termUn hT.branch hT.branchEx hT.tryT hT.tryUn hT.tryIndT hT.tryIndUn
    hM6 hRef (fun s' => driverSem_csem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_csem (hX s'))
    (fun s' => indCallsRefine_csem (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols)) hmem
    (fun s' => memRefinesFP_csem _ (F s') (ctx s') (X s') (hslotB s')) houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

/-- **The typed final theorem for an `AllocChecked` allocation** (`backend_correct_final_ex`
for the typed scope): the Arm run of the compiled function refines the CLIF run, each returned
value in the ABI return register of its class (`ArmRefinesT`). Premises: those of
`backend_correct_final_ex` with `InSubsetT`/`CompiledAT`, and the typed M4 families
`TypedRules`. -/
theorem backend_correct_final_exT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledAT f k vc vcp rf af fa fb) (hT : TypedRules)
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
  backend_correct_m4_exT (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc hT
    (regLevelCorrect_backend_ex hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallAT hc h)) (fun h => hTls (hasTls_of_vcodeAT hc h)))
    (refines_final K vcp rf af fa X) hX hXI (fun _ => hsym)
    (fun _ => memRefines_csem _ _ X hslot hsym) (fun _ => hslot) (outgoing_le_intBaseAT hc)
    hent hres hbe hargs (stackArgsAvoid_frameWAT hc hres hent hargs) hcs hrel htr fuel

/-- **The typed final theorem** (`backend_correct_final` for the typed scope: `CompiledT`, the
allocation accepted by `checkAlloc`). -/
theorem backend_correct_finalT {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubsetT p f) (hc : CompiledT f k vc vcp rf af fa fb) (hT : TypedRules)
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
  backend_correct_final_exT hsub hc.toA hT hcov hC hCT hTls hX hXI hsym hslot hent hres hbe hargs
    hcs hrel htr fuel

/-- **Integer specialization of the typed final theorem**: `backend_correct_final`'s premises
(`InSubset`, `Compiled`) and conclusion (`ArmRefines`), derived through the typed chain
(`InSubset.toT`, `Compiled.toT`, the integer returns of a subset-E signature). -/
theorem backend_correct_final_ofT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : Compiled f k vc vcp rf af fa fb) (hT : TypedRules)
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
    ArmRefines fb base ra (ArmStepX X H fa) s (Clif.runLoop env p fuel cs) := by
  have hcA := hc.toT.toA
  exact backend_correct_of_rules_ex_ofT hsub.toT hcA (functionE_sig_int hsub.subsetE).2
    lowerRulesCorrectTI_program lowerRulesCorrectT_program lowerRulesCorrectFT_program
    nonEUnmatchableT_program hT.callsT hT.indT memRulesCorrectRTI_program
    memRulesCorrectRT_program hT.term hT.termUn hT.branch hT.branchEx hT.tryT hT.tryUn hT.tryIndT
    hT.tryIndUn
    (regLevelCorrect_backend_ex hcA.check hcA.alloc hcA.emit hcA.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallAT hcA h)) (fun h => hTls (hasTls_of_vcodeAT hcA h)))
    (refines_final K vcp rf af fa X)
    (fun s' => driverSem_csem _ _ X)
    (fun s' => callsRefine_csem (hX s'))
    (fun s' => indCallsRefine_csem (hXI s') hsym (fun _ _ _ h => h.1.symbols))
    (fun _ => memRefines_csem _ _ X hslot hsym)
    (fun s' => memRefinesFP_csem _ _ _ X hslot) (outgoing_le_intBaseAT hcA)
    hent hres hbe hargs (stackArgsAvoid_frameWAT hcA hres hent hargs) hcs hrel htr fuel

end E2E
