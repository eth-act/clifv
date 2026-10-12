import FV.E2E.Main
import FV.Backend.Proof.DeadCleanupPrepare

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- The legacy lowering followed by the proved conservative cleanup.
The lowering validator still checks the raw lowering output. -/
structure CompiledCleanup (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheck f vc = true
  prepare : prepare (Backend.DeadCleanup.prune vc) = .ok vcp
  prepOk : prepCheck (Backend.DeadCleanup.prune vc) vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `Compiled` with the allocation premise `AllocChecked` (verified in-states, `CheckedAt`, with an
`EntryOk` entry state) in place of `checkAlloc`'s verdict (V4): the allocation need not come from
regalloc2 and be accepted by the checker's own fixpoint iteration (the spill allocation,
`FV/E2E/AllocDirect.lean`). `CompiledCleanup.toA`: every `Compiled` is one. -/
structure CompiledCleanupA (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheck f vc = true
  prepare : prepare (Backend.DeadCleanup.prune vc) = .ok vcp
  prepOk : prepCheck (Backend.DeadCleanup.prune vc) vcp = true
  check : AllocChecked vcp rf
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

theorem CompiledCleanup.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanup f k vc vcp rf af fa fb) :
    CompiledCleanupA f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, allocChecked_of_checkAlloc hc.check, hc.alloc, hc.emit,
    hc.layout⟩


theorem backend_correct_cleanup_ex {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
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
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr⟩ := loweringObligations_of_check hc.lowerOk
  refine backend_correct_of_layers_ex (fun s' => iselSim_of_driver (ctx := ctx) (st0 := st0) (R := R)
    (gn := gn) (bl := bl) (A := A) ?_ (hds s') (hmem s')) (fun s' a w => by
      obtain ⟨hr, ht⟩ := prune_correct (vc := vc) (hPure s') a w
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


theorem backend_correct_of_rules_cleanup_ex {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
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
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_cleanup_ex hsub hc hrules hex hcallRules hindRules hmemRules
    (fun s' => termCalls_of_rules htermRules htermUn hbranch hbranchEx (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f))
    (fun s' => tryCalls_of_rules htryRules htryUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s'))
    (fun s' => tryIndCalls_of_rules htryIndRules htryIndUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hicalls s'))
    hM6 hRef hds hcalls hicalls hmem hPure houtB hent hres hbe hargs hargF hcs hrel htr fuel


end E2E
