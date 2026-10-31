import FV.E2E.SretReturn
import FV.E2E.SretReturnWitness
import FV.E2E.DeadCleanupPipeline
import FV.E2E.DeadCleanupContracts
import FV.E2E.DeadCleanupRegLevel
import FV.E2E.DeadCleanupFinal
import FV.E2E.NonVacuity

/-!
# The `sret` return register through the dead-cleanup variant (S7)

The dead-cleanup chain (`backend_correct_final_cleanup` and its stages, `ArmRefines`) claims the
CLIF return values and the memory; the `_abi` copies also claim the ABI return values after them
(`ArmRefinesAbi`, `sretArg f args`, the conclusion of `backend_correct_final_abi`), with the extra
premise `sretStableB f = true` (the `sret` value is bound once):

* `backend_correct_cleanup_ex_abi`: the rules-level `backend_correct_cleanup_ex` with
  `IselSimAbi` (`iselSimAbi_of_driver`) under the cleanup `prune_correct` prepare step;
* `backend_correct_of_rules_cleanup_ex_abi`, `backend_correct_m4_cleanup_ex_abi`,
  `backend_correct_final_cleanup_ex_abi`, **`backend_correct_final_cleanup_abi`**;
* **`backend_correct_final_cleanup_sret`**: for a function with an `sret` parameter `i` and no
  returns, a CLIF return is matched by an Arm return with `args[i]` in x0;
* `SretReturnCleanup.compiled_cleanup_exists`, `sw_returns_sret_cleanup`: non-vacuity, on
  `SretReturnWitness.sw` (compiled through the dead-cleanup pipeline).
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- The rules-level dead-cleanup `backend_correct` with the ABI return values
(`backend_correct_cleanup_ex` for `IselSimAbi`). -/
theorem backend_correct_cleanup_ex_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (hS : sretStableB f = true)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M4
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcallRules : CallRulesCorrect Isle.Aarch64.program)
    (hindRules : IndRulesCorrect Isle.Aarch64.program)
    (hmemRules : MemRulesCorrect Isle.Aarch64.program)
    (hterms : ∀ s, TermCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w))
    (htries : ∀ s, TryCalls f (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env p out)
    (htryInds : ∀ s, TryIndCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env p (indSigs f))
    -- M6 + M5
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    -- the shared VCode semantics (M6's `csem`)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    -- the callee contract (M6, from `CalleeSound`)
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    -- the indirect-call contract (M6, from `XCallsIndOk`)
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    -- the memory forms (M6: loads/stores/`loadAddr`/GOT loads of `csem` with slot base `slotOff`
    -- and the link-time symbol addresses `syms`)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    -- the outgoing stack-argument area of the relation holds every call's stack arguments
    (hPure : ∀ s i us w outs w' ctl, pureForm i = true →
      sem s i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  refine backend_correct_of_layers_ex_abi (fun s' => iselSimAbi_of_driver (ctx := ctx) (st0 := st0)
    (R := R) (gn := gn) (bl := bl) (A := A) ?_ (hds s') (hmem s') hS) (fun s' a w => by
      obtain ⟨hr, ht⟩ := prune_correct (vc := vc) (hPure s') (hCmp s') a w
      obtain ⟨pr, pt⟩ := prepareCorrect_of_check (hds s') hc.prepOk a w
      exact ⟨fun _ _ _ h => pr _ _ _ (hr _ _ _ h), fun _ h => pt _ (ht _ h)⟩)
    hM6 hent hres hbe
    (argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe hargs hargF)
    hcs hrel htr fuel
  exact {
    shape := hshape
    cert := hcert
    dsem := (hds s').toDriverSemG
    insts := instCalls_of_rules hrules hex hcallRules hindRules hmemRules (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s') (hicalls s') (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB)
      (memRelOk_holds ⟨F s', syms, slotOff, out⟩ f)
    terms := hterms s'
    ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
    indSig := indSig_of_subset hsub
    subE := hsub.subsetE
    entryLocs := entryOk_of_check hc.lowerOk
    brIdx := hbr
    noTail := noTail_of_subset hsub
    tries := ⟨out, htries s', tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
    tryExt := hsub.tryExterns
    tryInd := htryInds s'
    tryIndSig := tryIndSig_of_subset hsub
    cfg := by
      obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
      exact ⟨ss, ps, (prune_cfg vc).symm.trans he⟩ }

/-- `backend_correct_of_rules_cleanup_ex` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_of_rules_cleanup_ex_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (hS : sretStableB f = true)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M4
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcallRules : CallRulesCorrect Isle.Aarch64.program)
    (hindRules : IndRulesCorrect Isle.Aarch64.program)
    (hmemRules : MemRulesCorrect Isle.Aarch64.program)
    (htermRules : LowerTermRulesCorrect Isle.Aarch64.program)
    (htermUn : TermUnmatchable Isle.Aarch64.program)
    (hbranch : BranchRulesCorrect Isle.Aarch64.program)
    (hbranchEx : BranchExcludedUnmatchable Isle.Aarch64.program)
    (htryRules : TryRulesCorrect Isle.Aarch64.program)
    (htryUn : TryUnmatchable Isle.Aarch64.program)
    (htryIndRules : TryIndRulesCorrect Isle.Aarch64.program)
    (htryIndUn : TryIndUnmatchable Isle.Aarch64.program)
    -- M6 + M5
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    -- the shared VCode semantics (M6's `csem`)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    -- the callee contract (M6, from `CalleeSound`)
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    -- the indirect-call contract (M6, from `XCallsIndOk`)
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    -- the memory forms (M6: loads/stores/`loadAddr`/GOT loads of `csem` with slot base `slotOff`
    -- and the link-time symbol addresses `syms`)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    -- the outgoing stack-argument area of the relation holds every call's stack arguments
    (hPure : ∀ s i us w outs w' ctl, pureForm i = true →
      sem s i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_cleanup_ex_abi hsub hc hS hrules hex hcallRules hindRules hmemRules
    (fun s' => termCalls_of_rules htermRules htermUn hbranch hbranchEx (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f))
    (fun s' => tryCalls_of_rules htryRules htryUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s'))
    (fun s' => tryIndCalls_of_rules htryIndRules htryIndUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f)
      (indStack_mono (indStack_of_check hc.lowerOk) houtB) (hicalls s'))
    hM6 hRef hds hcalls hicalls hmem hPure hCmp houtB hent hres hbe hargs hargF hcs hrel htr fuel

/-- `backend_correct_m4_cleanup_ex` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_m4_cleanup_ex_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (hS : sretStableB f = true)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
    -- M6 + M5
    (hM6 : RegLevelCorrectEx (fun s => valueSem (F s) (ctx s) (X s)) F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (valueSem (F s) (ctx s) (X s)))
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    -- the external contract of the indirect calls (their call-site signatures `indSigs f`;
    -- vacuous without indirect calls, `xCallsIndOk_nil`) and the linker's symbol addresses
    (hXI : ∀ s, XCallsIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (valueSem (F s) (ctx s) (X s)))
    -- the relation's outgoing stack-argument area holds every call's stack arguments
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra astep s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_of_rules_cleanup_ex_abi hsub hc hS
    lowerRulesCorrect_program excludedUnmatchable callRulesCorrect indRulesCorrect
    memRulesCorrect_program lowerTermRulesCorrect termUnmatchable branchRulesCorrect
    branchExcludedUnmatchable tryRulesCorrect tryUnmatchable tryIndRulesCorrect tryIndUnmatchable
    hM6 hRef (fun s' => driverSem_valueSem (F s') (ctx s') (X s'))
    (fun s' => callsRefine_valueSem (hX s'))
    (fun s' => indCallsRefine_valueSem (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols)) hmem
    (fun _ _ _ _ _ _ _ hp he => valueSem_pure hp he) (fun _ => valueSem_cmpOverwrite _ _ _) houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

/-- `backend_correct_final_cleanup_ex` with the ABI return values (`sretStableB f`). -/
theorem backend_correct_final_cleanup_ex_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (hS : sretStableB f = true)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    -- the straight-line forms of the prepared VCode are covered (decided by `formsCoveredB`)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    -- the callee contract of the machine's call hook (AAPCS64)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    -- the callee contract of the call of a `try_call` (only for a function with one)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    -- the TLSDESC contract of the machine's `tls_value` hook (only for a function with one)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- the external contract of the indirect calls of `f` (`call_indirect`, `try_call_indirect`:
    -- the externs at their link-time addresses, with the call sites' signatures; vacuous
    -- without indirect calls, `xCallsIndOk_nil`)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- memory forms (`memRefines_valueSem`): the external semantics' symbol addresses are the linked
    -- ones, and the relation's slot-region offset is the frame's slot base
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra (ArmStepX X H fa) s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_m4_cleanup_ex_abi (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc
    hS
    (regLevelCorrect_backend_ex_value hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallCleanupA hc h)) (fun h => hTls (hasTls_of_vcodeCleanupA hc h)))
    (fun _ => refines_valueSem _ _ X) hX hXI (fun _ => hsym)
    (fun _ => memRefines_valueSem _ _ X hslot hsym) (outgoing_le_intBaseCleanupA hc)
    hent hres hbe hargs (stackArgsAvoid_frameWCleanupA hc hres hent hargs) hcs hrel htr fuel

/-- **The dead-cleanup end-to-end theorem with the ABI return values**: `backend_correct_final_cleanup`
(its premises plus `sretStableB f`), and a return also leaves the ABI return values after the
CLIF ones in x0..: for a function with an `sret` parameter and no returns, the `sret` argument in
x0 (`sretArg`, `backend_correct_final_cleanup_sret`). -/
theorem backend_correct_final_cleanup_abi {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hS : sretStableB f = true)
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    -- the straight-line forms of the prepared VCode are covered (decided by `formsCoveredB`)
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    -- the callee contract of the machine's call hook (AAPCS64)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    -- the callee contract of the call of a `try_call` (only for a function with one)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    -- the TLSDESC contract of the machine's `tls_value` hook (only for a function with one)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- the external contract of the indirect calls of `f` (`call_indirect`, `try_call_indirect`:
    -- the externs at their link-time addresses, with the call sites' signatures; vacuous
    -- without indirect calls, `xCallsIndOk_nil`)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- memory forms (`memRefines_csem`): the external semantics' symbol addresses are the linked
    -- ones, and the relation's slot-region offset is the frame's slot base
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefinesAbi fb base ra (ArmStepX X H fa) s (sretArg f args) (Clif.runLoop env p fuel cs) :=
  backend_correct_final_cleanup_ex_abi hsub hc.toA hS hcov hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel

/-- **The `sret` return register through the dead-cleanup variant**: for a function with an
`sret` parameter `i` and no returns, under the premises of `backend_correct_final_cleanup_abi`,
a CLIF return is matched by an Arm return (`ArmRet`) whose x0 holds the `sret` argument
`args[i]`, with the memory the function wrote (`MemAgree`). -/
theorem backend_correct_final_cleanup_sret {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hS : sretStableB f = true)
    {i : Nat} (hi : f.sig.params.findIdx? (·.purpose == .sret) = some i)
    (hnr : f.sig.returns = [])
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
    (htr : TrapsExplicit env p cs) (fuel : Nat) {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop env p fuel cs = .returned vals cm) {v : Clif.Val}
    (hv : args[i]? = some v) :
    ∃ n, ArmRet ra s (runX (ArmStepX X H fa) n s) ∧
      XHolds v (xreg 0 (runX (ArmStepX X H fa) n s)) ∧
      MemAgree cm (runX (ArmStepX X H fa) n s) := by
  obtain ⟨B0, hentB, hbody, hterm, -, -⟩ := hcs.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hentB
  have hvals : vals = [] := by
    have := runLoop_returned_tys_entry hsub.externCalls hsub.tryExterns (noTail_of_subset hsub)
      (runPrem_of_entry hcs htr) (sretStable_of hS) hB0 hcs.callers hcs.func hbody hterm hrun
    rw [hnr] at this
    simpa [Clif.AbiParam.tys] using this
  subst hvals
  have h := backend_correct_final_cleanup_abi hsub hc hS hcov hC hCT hTls hX hXI hsym hslot
    hent hres hbe hargs hcs hrel htr fuel
  rw [hrun, sretArg_of_sret hi hnr, hv] at h
  obtain ⟨n, hret, hx, hm⟩ := h
  exact ⟨n, hret, hx 0 v (by simp), hm⟩

end E2E

namespace E2E.SretReturnCleanup

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup
open E2E.SretReturnWitness

/-- `sw` compiled through the dead-cleanup pipeline, with the prepared forms covered. -/
def checksCleanup : Bool :=
  sretStableB sw &&
  match lowerFunction sw with
  | .error _ => false
  | .ok vc =>
    lowerCheck sw vc &&
    match Backend.prepare (Backend.DeadCleanup.prune vc) with
    | .error _ => false
    | .ok vcp =>
      prepCheck (Backend.DeadCleanup.prune vc) vcp && (checkAlloc vcp (spillAlloc vcp)).isOk &&
      match lowerRFunc vcp (spillAlloc vcp) with
      | .error _ => false
      | .ok af => match emitFunc 0 af with
        | .error _ => false
        | .ok fa => formsCoveredB ⟨fa.k, af.slotBase⟩ vcp && fa.layout.isOk

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- The closed test receipt (not used by any compiler correctness theorem). -/
theorem checksCleanup_true : checksCleanup = true := by native_decide

set_option maxHeartbeats 10000000 in
/-- `sw` is in scope (decided; as in `SretReturnWitness`). -/
theorem verifiable_sw : Backend.verifiable sw = true := by native_decide

/-- **`sw` meets the compile-time premises of `backend_correct_final_cleanup_sret`** (`i = 0`). -/
theorem compiled_cleanup_exists :
    InSubset ({ funcs := [] } : Clif.Program) sw ∧ sretStableB sw = true ∧
    sw.sig.params.findIdx? (·.purpose == .sret) = some 0 ∧ sw.sig.returns = [] ∧
    (∀ p v, sretArg sw [p, v] = [p]) ∧
    ∃ vc vcp af fa fb, CompiledCleanup sw 0 vc vcp (spillAlloc vcp) af fa fb ∧
      FormsCovered ⟨fa.k, af.slotBase⟩ vcp := by
  have h := checksCleanup_true
  simp only [checksCleanup, Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  refine ⟨InSubset.of_verifiable verifiable_sw (fun _ => rfl), hs, by decide,
    rfl, SretReturnWitness.sretArg_sw, ?_⟩
  cases hl : lowerFunction sw with
  | error e => rw [hl] at h; cases h
  | ok vc =>
    rw [hl] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hlo, h⟩ := h
    cases hp : Backend.prepare (Backend.DeadCleanup.prune vc) with
    | error e => rw [hp] at h; cases h
    | ok vcp =>
      rw [hp] at h
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hpr, hck⟩, h⟩ := h
      have hc : checkAlloc vcp (spillAlloc vcp) = .ok () := by
        cases he : checkAlloc vcp (spillAlloc vcp) with
        | error e => rw [he] at hck; cases hck
        | ok u => cases u; rfl
      cases ha : lowerRFunc vcp (spillAlloc vcp) with
      | error e => rw [ha] at h; cases h
      | ok af =>
        rw [ha] at h
        simp only at h
        cases he : emitFunc 0 af with
        | error e => rw [he] at h; cases h
        | ok fa =>
          rw [he] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨hcov, hlay⟩ := h
          cases hb : fa.layout with
          | error e => rw [hb] at hlay; cases hlay
          | ok fb =>
            exact ⟨vc, vcp, af, fa, fb, ⟨hl, hlo, hp, hpr, hc, ha, he, hb⟩,
              (formsCoveredB_iff _ _).1 hcov⟩

/-- **`backend_correct_final_cleanup_sret` applies to `sw`**: for its compilation through the
dead-cleanup pipeline, with the witness callees (`NonVacuity`; `sw` makes no calls), a CLIF return
of a run of `sw` on `[p, v]` is matched by an Arm return with the struct pointer `p` in x0. -/
theorem sw_returns_sret_cleanup :
    ∃ vc vcp af fa fb, CompiledCleanup sw 0 vc vcp (spillAlloc vcp) af fa fb ∧
      ∀ {syms : String → Option Nat} {K : Nat} {env : Clif.Env} (_ : 32 ≤ K) (g h tp : BitVec 64)
        {base ra : BitVec 64} {s w₀ : Arm.ArmState} {p v : Clif.Val} {cs : Clif.State},
        AbiEntry fb base ra s → StackAvail K af s → BodyEntry af s w₀ →
        ArgsIn sw.sig [p, v] s → ClifEntry sw [p, v] cs →
        Rel.holds ⟨frameW K (RAFrame.compute vcp (spillAlloc vcp)).intBase
          (RAFrame.compute vcp (spillAlloc vcp)).size af s, syms, af.slotBase,
          (RAFrame.compute vcp (spillAlloc vcp)).intBase⟩ sw cs.frame.slots cs.mem w₀ →
        TrapsExplicit env { funcs := [] } cs → ∀ fuel vals cm,
        Clif.runLoop env { funcs := [] } fuel cs = .returned vals cm →
        ∃ n, ArmRet ra s (runX (ArmStepX (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) fa) n s) ∧
          XHolds p (xreg 0 (runX (ArmStepX (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) fa) n s)) ∧
          MemAgree cm (runX (ArmStepX (witnessX (witnessSym syms) tp)
            (witnessHooks g h (witnessSym syms) tp) fa) n s) := by
  obtain ⟨hsub, hS, hi, hnr, -, vc, vcp, af, fa, fb, hc, hcov⟩ := compiled_cleanup_exists
  refine ⟨vc, vcp, af, fa, fb, hc, ?_⟩
  intro syms K env hK g h tp base ra s w₀ p v cs hent hres hbe hargs hcs hrel htr fuel vals cm hrun
  obtain ⟨hC, hTls, hX, hXI, hsym⟩ :=
    final_contracts_witness (f := sw) (vcp := vcp) (rf := spillAlloc vcp) (af := af)
      (slotOff := af.slotBase) (syms := syms) (env := env) hK g h tp
      (by simp [sw]) (by simp [indSigs, sw]) (by simp [sw]) (by simp [indSigs, sw])
  exact backend_correct_final_cleanup_sret hsub hc hS hi hnr hcov hC
    (fun ⟨B, hB, ht⟩ => absurd ht (by simp [sw] at hB; subst hB; decide)) (fun _ => hTls)
    hX hXI hsym rfl hent hres hbe hargs hcs hrel htr fuel hrun (v := p) rfl

end E2E.SretReturnCleanup
