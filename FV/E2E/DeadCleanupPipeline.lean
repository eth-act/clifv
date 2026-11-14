import FV.E2E.Main
import FV.Backend.Proof.DeadCleanupPrepare
import FV.E2E.CleanupStageIsel
import FV.E2E.RegLevelAllocAF

namespace E2E
open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- The legacy lowering followed by the production cleanup stage (`cleanupStage`: Cranelift's
skip of unused instructions, then the dead-producer cleanup). The lowering validator still checks
the raw lowering output. (The fields `prepare`/`prepOk` were about `DeadCleanup.prune vc`; the
compiler now runs `cleanupStage f vc` there.) -/
structure CompiledCleanup (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheck f vc = true
  prepare : prepare (cleanupStage f vc) = .ok vcp
  prepOk : prepCheck (cleanupStage f vc) vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `Compiled` with the allocation premise `AllocChecked` (verified in-states, `CheckedAt`, with an
`EntryOk` entry state) in place of `checkAlloc`'s verdict (V4): the allocation need not come from
regalloc2 and be accepted by the checker's own fixpoint iteration (the spill allocation,
`FV/E2E/AllocDirect.lean`). `CompiledCleanup.toA`: every `Compiled` is one. (Its
`prepare`/`prepOk` are about `cleanupStage f vc`, as `CompiledCleanup`'s.) -/
structure CompiledCleanupA (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheck f vc = true
  prepare : prepare (cleanupStage f vc) = .ok vcp
  prepOk : prepCheck (cleanupStage f vc) vcp = true
  check : AllocChecked vcp rf
  alloc : lowerRFunc vcp rf = .ok af
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

theorem CompiledCleanup.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanup f k vc vcp rf af fa fb) :
    CompiledCleanupA f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, allocChecked_of_checkAlloc hc.check, hc.alloc, hc.emit,
    hc.layout⟩

/-- Every argument of `sig` is passed in a register (`locsOf`): a frameless leaf has no incoming
stack argument (the lowering addresses those from the frame pointer, which a frameless leaf
does not set up). -/
def regArgsB (sig : Clif.Signature) : Bool :=
  (locsOf sig).all fun | .reg _ => true | .stack _ => false

theorem regArgsB_spec {sig : Clif.Signature} (h : regArgsB sig = true) :
    ∀ l ∈ locsOf sig, ∃ r, l = .reg r := by
  intro l hl
  have := List.all_eq_true.mp h l hl
  cases l with
  | reg r => exact ⟨r, rfl⟩
  | stack _ => cases this

/-- **`CompiledCleanup` with frameless leaves (#1028)**: the allocated function is `lowerRFunc`'s
output, or that output without its frame for a leaf (`AllocAF`, as `Backend.frameless` leaves
it under `preserve_frame_pointers=false`). Without a frame, the compiled code passes the leaf's
check (`FnAsm.leafChk`: no line but `ret` names `x29`/`x30`, so the function makes no call) and
every argument is passed in a register (`regArgsB`). Both are decided on the compiled objects. -/
structure CompiledCleanupL (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheck f vc = true
  prepare : prepare (cleanupStage f vc) = .ok vcp
  prepOk : prepCheck (cleanupStage f vc) vcp = true
  check : checkAlloc vcp rf = .ok ()
  alloc : AllocAF vcp rf af
  leaf : af.frame = false → fa.leafChk = true ∧ regArgsB f.sig = true
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

/-- `CompiledCleanupL` with the allocation premise `AllocChecked` (as `CompiledCleanupA`). -/
structure CompiledCleanupAL (f : Clif.Function) (k : Nat) (vc vcp : VCode) (rf : RFunc) (af : AFunc)
    (fa : FnAsm) (fb : FnBin) : Prop where
  lower : lowerFunction f = .ok vc
  lowerOk : lowerCheck f vc = true
  prepare : prepare (cleanupStage f vc) = .ok vcp
  prepOk : prepCheck (cleanupStage f vc) vcp = true
  check : AllocChecked vcp rf
  alloc : AllocAF vcp rf af
  leaf : af.frame = false → fa.leafChk = true ∧ regArgsB f.sig = true
  emit : emitFunc k af = .ok fa
  layout : fa.layout = .ok fb

theorem CompiledCleanupL.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupL f k vc vcp rf af fa fb) :
    CompiledCleanupAL f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, allocChecked_of_checkAlloc hc.check, hc.alloc,
    hc.leaf, hc.emit, hc.layout⟩

/-- Every `CompiledCleanupA` is a `CompiledCleanupAL` (it has a frame: no leaf premise). -/
theorem CompiledCleanupA.toL {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupA f k vc vcp rf af fa fb) :
    CompiledCleanupAL f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, hc.check, AllocAF.of_lowerRFunc hc.alloc,
    fun hf => absurd (lowerRFunc_frame hc.alloc) (by rw [hf]; decide), hc.emit, hc.layout⟩

/-- A `CompiledCleanupAL` with a frame is a `CompiledCleanupA`. -/
theorem CompiledCleanupAL.toA {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc}
    {fa : FnAsm} {fb : FnBin} (hc : CompiledCleanupAL f k vc vcp rf af fa fb) (hf : af.frame = true) :
    CompiledCleanupA f k vc vcp rf af fa fb :=
  ⟨hc.lower, hc.lowerOk, hc.prepare, hc.prepOk, hc.check, hc.alloc.lowerRFunc_of_frame hf, hc.emit,
    hc.layout⟩

/-- `argsAtEntry_body` with or without a frame: a frameless function takes every argument in a
register (`regArgsB`), which the prologue-free entry keeps. -/
theorem argsAtEntry_bodyL {f : Clif.Function} {args : List Clif.Val} {af : AFunc}
    {s w₀ : Arm.ArmState} {F : BitVec 64 → Prop} (hleaf : af.frame = false → regArgsB f.sig = true)
    (hregs : ∀ l ∈ locsOf f.sig, ∀ r, l = .reg r → ∃ n, r = .x n ∧ n ≤ 8)
    (hbe : BodyEntry af s w₀) (h : ArgsIn f.sig args s) (hav : StackArgsAvoid F f.sig args s)
    {K : Nat} (hres : StackAvail K af s) :
    ArgsAtEntry F f.sig args w₀ := by
  cases hf : af.frame
  · intro loc v hm
    have hl : loc ∈ locsOf f.sig := (List.of_mem_zip hm).1
    have h1 := h loc v hm
    obtain ⟨r, rfl⟩ := regArgsB_spec (hleaf hf) _ hl
    obtain ⟨n, rfl, hn⟩ := hregs _ hl _ rfl
    simp only at h1 ⊢
    rw [regVal_x, show xreg n w₀ = xreg n s from hbe.args n (by omega)]
    exact h1
  · exact argsAtEntry_body hf hregs hbe h hav hres


theorem backend_correct_cleanup_exL {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupAL f k vc vcp rf af fa fb)
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
    -- a compare's flags are overwritten by the next compare (the cleanup drops compares whose
    -- flags are dead, #552)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hsk⟩ := skipStage_spec hc.lowerOk
  refine backend_correct_of_layers_ex (fun s' => iselSim_of_driver_stage (ctx := ctx) (st0 := st0)
    (R := R) (gn := gn) (bl := bl) (A := A) ?_ hsk (hds s') (hmem s')) (fun s' a w => by
      obtain ⟨hr, ht⟩ := prune_correct (vc := skipStage f vc) (hPure s') (hCmp s') a w
      obtain ⟨pr, pt⟩ := prepareCorrect_of_check (hds s') hc.prepOk a w
      exact ⟨fun _ _ _ h => pr _ _ _ (hr _ _ _ h), fun _ h => pt _ (ht _ h)⟩)
    hM6 hent hres hbe
    (argsAtEntry_bodyL (fun hf => (hc.leaf hf).2) (entryRegs_of_check hc.lowerOk) hbe hargs hargF hres)
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
      exact ⟨ss, ps, (cleanupStage_cfg f vc).symm.trans he⟩ }

theorem backend_correct_cleanup_ex {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
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
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hPure : ∀ s i us w outs w' ctl, pureForm i = true →
      sem s i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_cleanup_exL hsub hc.toL hrules hex hcallRules hindRules hmemRules hterms htries
    htryInds hM6 hRef hds hcalls hicalls hmem hPure hCmp houtB hent hres hbe hargs hargF hcs hrel htr
    fuel


theorem backend_correct_of_rules_cleanup_exL {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupAL f k vc vcp rf af fa fb)
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
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_cleanup_exL hsub hc hrules hex hcallRules hindRules hmemRules
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

theorem backend_correct_of_rules_cleanup_ex {p : Clif.Program} {f : Clif.Function} {k : Nat} {vc vcp : VCode}
    {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    {sem : Arm.ArmState → Sem} {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.Env}
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
    (hM6 : RegLevelCorrectEx sem F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hPure : ∀ s i us w outs w' ctl, pureForm i = true →
      sem s i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    (houtB : vc.outgoing ≤ out)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicit env p cs) (fuel : Nat) :
    ArmRefines fb base ra astep s (Clif.runLoop env p fuel cs) :=
  backend_correct_of_rules_cleanup_exL hsub hc.toL hrules hex hcallRules hindRules hmemRules
    htermRules htermUn hbranch hbranchEx htryRules htryUn htryIndRules htryIndUn hM6 hRef hds hcalls
    hicalls hmem hPure hCmp houtB hent hres hbe hargs hargF hcs hrel htr fuel


end E2E
