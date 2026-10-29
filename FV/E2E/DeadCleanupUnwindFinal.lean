import FV.E2E.DeadCleanupUnwind
import FV.E2E.DeadCleanupUnwindIsel
import FV.E2E.DeadCleanupUnwindRegLevel
import FV.E2E.IselSimU
import FV.Backend.Proof.LowerSimUCheck
import FV.E2E.DeadCleanupFinal

/-!
# The shipped compiler's per-function theorem with unwinding (S10e, #232)

The dead-cleanup chain of `FV/E2E/DeadCleanupPipeline.lean`/`FV/E2E/DeadCleanupFinal.lean` with
the exceptional edge, layer for layer:

* `backend_correct_cleanup_exU` (`backend_correct_cleanup_ex`): CLIF → VCode by
  `iselSimU_of_driver` (the lowering validated by `lowerCheckU`), `prune` + `prepare` by
  `prepareCorrectU_cleanup`, the register level as a premise (`RegLevelCorrectUEx`);
* `backend_correct_of_rules_cleanup_exU` (`backend_correct_of_rules_cleanup_ex`): the terminator
  and `try_call` premises from the rules;
* `backend_correct_m4_cleanup_exU` (`backend_correct_m4_cleanup_ex`): the value semantics with
  unwinding `valueSemU`, its M4 facts from `FV/E2E/UnwindValueSem.lean`;
* **`backend_correct_final_cleanup_unwind_ex`**, **`backend_correct_final_cleanup_unwind`**
  (`backend_correct_final_cleanup{,_ex}`): the register level by
  `regLevelCorrect_backend_exU_value`; the premises of the old theorem plus the lowering's
  unwinding validator, the raising callees' contracts (`CalleeUnwOkG`, `XRaiseOk`,
  `XRaiseIndOk`), the emitted call-site table and frame rows the unwinder reads, and the
  decidable checks `padsNonzeroB`, `lastCallsOk`, `savedCheck`. The conclusion is
  `ArmRefinesU` of the CLIF run with unwinding (`Clif.runLoopX`) on the machine with unwinding
  (`Unw.ArmStepU`).
* **`backend_correct_final_cleanup_unwind_ex_any`**, **`backend_correct_final_cleanup_unwind_any`**:
  the same without `lastCallsOk` (#622: the call-site bridge holds for every block since #553);
  the theorems above are their corollaries.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup Backend.Proof.UnwindTables

/-- **`backend_correct_cleanup_ex` with unwinding**: any semantics with the M4 facts, the
raising-call facts (`RaiseSem`) and pure producers that keep the world. -/
theorem backend_correct_cleanup_exU {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {sem : Arm.ArmState → Sem} {X : Arm.ArmState → ExtSem} {XR : XRaise}
    {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.XEnv}
    -- M4
    (hrules : LowerRulesCorrect Isle.Aarch64.program)
    (hex : ExcludedUnmatchable Isle.Aarch64.program)
    (hcallRules : CallRulesCorrect Isle.Aarch64.program)
    (hindRules : IndRulesCorrect Isle.Aarch64.program)
    (hmemRules : MemRulesCorrect Isle.Aarch64.program)
    (hterms : ∀ s, TermCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w))
    (htries : ∀ s, TryCalls f (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env.toEnv p out)
    (htryInds : ∀ s, TryIndCalls (sem s) (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w)
      env.toEnv p (indSigs f))
    -- M6 + M5
    (hM6 : RegLevelCorrectUEx sem XR F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env.toEnv (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env.toEnv (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hPure : ∀ s i us w outs w' ctl, pureForm i = true →
      sem s i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    -- the raising calls: the semantics, the callees' exceptional results
    (hRS : ∀ s, RaiseSem (F s) (X s) XR (sem s))
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s) XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s) XR)
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra astep s (Clif.runLoopX env p fuel cs.toX) := by
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUs⟩ := loweringU_of_check hlU
  refine backend_correct_cleanup_layersU_ex hc (fun s' => iselSimU_of_driver (ctx := ctx)
      (st0 := st0) (R := R) (gn := gn) (bl := bl) (A := A) ?_ hUs (hds s') (hRef s') (hmem s')
      (hRS s') (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
      (tryStack_mono (tryStack_of_check hc.lowerOk) houtB) (hXR s') (hXRi s') (hsym s'))
    hds hPure hCmp hM6 hent hres hbe hargs hargF hcs hrel htr fuel
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

/-- **`backend_correct_of_rules_cleanup_ex` with unwinding**: the terminator and `try_call`
premises from the rules. -/
theorem backend_correct_of_rules_cleanup_exU {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {sem : Arm.ArmState → Sem} {X : Arm.ArmState → ExtSem} {XR : XRaise}
    {F : Arm.ArmState → BitVec 64 → Prop}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.XEnv}
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
    (hM6 : RegLevelCorrectUEx sem XR F K astep vcp af fb)
    (hRef : ∀ s, Refines (F s) (sem s)) (hds : ∀ s, DriverSem (sem s))
    (hcalls : ∀ s, CallsRefine (F s) env.toEnv (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hicalls : ∀ s, IndCallsRefine env.toEnv (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (sem s))
    (hmem : ∀ s, MemRefines (F s) slotOff syms (sem s))
    (hPure : ∀ s i us w outs w' ctl, pureForm i = true →
      sem s i us w = some (outs, w', ctl) → w' = w ∧ ctl = .next)
    (hCmp : ∀ s, CmpOverwrite (sem s))
    (hRS : ∀ s, RaiseSem (F s) (X s) XR (sem s))
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s) XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s) XR)
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra astep s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_cleanup_exU hsub hc hlU hrules hex hcallRules hindRules hmemRules
    (fun s' => termCalls_of_rules htermRules htermUn hbranch hbranchEx (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f))
    (fun s' => tryCalls_of_rules htryRules htryUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hmem s')
      (outArgsOk_holds ⟨F s', syms, slotOff, out⟩ f) (hcalls s'))
    (fun s' => tryIndCalls_of_rules htryIndRules htryIndUn (hRef s')
      (mrStable_holds ⟨F s', syms, slotOff, out⟩ f) (hicalls s'))
    hM6 hRef hds hcalls hicalls hmem hPure hCmp hRS hXR hXRi hsym houtB hent hres hbe hargs hargF hcs
    hrel htr fuel

/-- **`backend_correct_m4_cleanup_ex` with unwinding**: the value semantics with unwinding. The
callees that return normally do not raise (`hexcl`, `CalleeUnwOkG.excl`). -/
theorem backend_correct_m4_cleanup_exU {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {F : Arm.ArmState → BitVec 64 → Prop} {ctx : Arm.ArmState → FnCtx}
    {X : Arm.ArmState → ExtSem} {XR : XRaise}
    {syms : String → Option Nat} {slotOff out K : Nat} {astep : Arm.ArmState → Arm.ArmState}
    {env : Clif.XEnv}
    -- M6 + M5
    (hM6 : RegLevelCorrectUEx (fun s => valueSemU (F s) (ctx s) (X s) XR) XR F K astep vcp af fb)
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s))
    (hsym : ∀ s n b, syms n = some b → (X s).sym n 0 = BitVec.ofNat 64 b)
    (hmem : ∀ s, MemRefines (F s) slotOff syms (valueSemU (F s) (ctx s) (X s) XR))
    -- the raising callees
    (hexcl : ∀ s d uses w, (X s).call d uses w ≠ none → XR.raise d uses w = none)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2))
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s) XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f)
      (fun sl cm w => Rel.holds ⟨F s, syms, slotOff, out⟩ f sl cm w) (X s) XR)
    (houtB : vc.outgoing ≤ out)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hargF : StackArgsAvoid (F s) f.sig args s)
    (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨F s, syms, slotOff, out⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra astep s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_of_rules_cleanup_exU hsub hc hlU
    lowerRulesCorrect_program excludedUnmatchable callRulesCorrect indRulesCorrect
    memRulesCorrect_program lowerTermRulesCorrect termUnmatchable branchRulesCorrect
    branchExcludedUnmatchable tryRulesCorrect tryUnmatchable tryIndRulesCorrect tryIndUnmatchable
    hM6 (fun _ => refines_valueSemU _ _ _ _) (fun _ => driverSem_valueSemU _ _ _ _)
    (fun s' => callsRefine_valueSemU (hX s') (hexcl s'))
    (fun s' => indCallsRefine_valueSemU (hXI s') (hsym s') (fun _ _ _ h => h.1.symbols) (hexcl s'))
    hmem (fun _ _ _ _ _ _ _ hp he => valueSemU_pure hp he) (fun _ => valueSemU_cmpOverwrite _ _ _ _)
    (fun _ => raiseSem_valueSemU _ _ _ _) hXR hXRi hsym houtB
    hent hres hbe hargs hargF hcs hrel htr fuel

/-- **The shipped compiler's per-function theorem with unwinding, an `AllocChecked` allocation,
without the check on the calls of the last block** (#622; `regLevelCorrect_backend_exU_value_any`).
Non-vacuity: its premises are among `backend_correct_final_cleanup_unwind_ex`'s
(`DeadCleanupUnwindWitness`). -/
theorem backend_correct_final_cleanup_unwind_ex_any {p : Clif.Program} {f : Clif.Function}
    {k : Nat} {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_m4_cleanup_exU (ctx := fun _ => ⟨fa.k, af.slotBase⟩) (X := fun _ => X) hsub hc hlU
    (regLevelCorrect_backend_exU_value_any hc.check hc.alloc hc.emit hc.layout hcov hC
      (fun h => hCT (hasTry_of_hasTryCallCleanupA hc h)) (fun h => hTls (hasTls_of_vcodeCleanupA hc h))
      hU hsites hlsda hpad hrows hcie hfde hsaved)
    hX hXI (fun _ => hsym) (fun _ => memRefines_valueSemU _ _ X XR hslot hsym)
    (fun _ => (hU base s).excl) hXR hXRi (outgoing_le_intBaseCleanupA hc)
    hent hres hbe hargs (stackArgsAvoid_frameWCleanupA hc hres hent hargs) hcs hrel htr fuel

/-- **The shipped compiler's per-function theorem with unwinding without the check on the calls
of the last block** (#622; `backend_correct_final_cleanup_unwind`'s premises minus
`lastCallsOk`): for a function compiled through the dead cleanup (`CompiledCleanup`) whose
lowering passes the unwinding validator, every outcome of the CLIF run with unwinding is matched
by the run of the machine with unwinding. Non-vacuity: `DeadCleanupUnwindWitness` (its premises
are among `backend_correct_final_cleanup_unwind`'s). -/
theorem backend_correct_final_cleanup_unwind_any {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_final_cleanup_unwind_ex_any hsub hc.toA hlU hcov hC hCT hTls hU hX hXI hXR hXRi
    hsym hslot hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe hargs hcs hrel htr fuel

/-- **The shipped compiler's per-function theorem with unwinding** (`backend_correct_final_cleanup_ex`
with the exceptional edge, an `AllocChecked` allocation; statement kept for its callers,
`backend_correct_final_cleanup_unwind_ex_any` drops `lastCallsOk`). -/
theorem backend_correct_final_cleanup_unwind_ex {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    -- the lowering's unwinding validator (the landing pads, `try_call` shapes)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
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
    -- the raising callees' contract on the machine (unwinder, personality: `FV/Unw/Model.lean`)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    -- the external contract (callees of `f`, linker)
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    -- the external contract of the raising callees (their exceptional results)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    -- memory forms: the external semantics' symbol addresses are the linked ones, and the
    -- relation's slot-region offset is the frame's slot base
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    -- the tables the unwinder reads: the emitted call-site table (LSDA) and frame rows
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    -- the decidable checks: landing pads at non-zero offsets, the call-site bridge, the frame
    -- invariant at the calls
    (hpad : padsNonzeroB af fa = true) (_hlast : lastCallsOk af fa = true)
    (hsaved : savedCheck vcp rf = true)
    -- the run
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_final_cleanup_unwind_ex_any hsub hc hlU hcov hC hCT hTls hU hX hXI hXR hXRi
    hsym hslot hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe hargs hcs hrel htr fuel

/-- **The shipped compiler's per-function theorem with unwinding** (`backend_correct_final_cleanup`
with the exceptional edge): for a function compiled through the dead cleanup (`CompiledCleanup`)
whose lowering passes the unwinding validator, every outcome of the CLIF run with unwinding —
including an exception leaving the function (`unwound`) — is matched by the run of the machine
with unwinding (statement kept for its callers; `backend_correct_final_cleanup_unwind_any` drops
`lastCallsOk`). -/
theorem backend_correct_final_cleanup_unwind {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanup f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true)
    {X : ExtSem} {H : ArmHooks} {XR : XRaise} {U : Unw.UnwHooks} {T : Unw.FnTables}
    {syms : String → Option Nat} {slotOff : Nat} {env : Clif.XEnv} {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hCT : (∃ B ∈ f.blocks, B.term.isTry = true) → ∀ s, CalleeTryOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) X H vcp.TrySite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hU : ∀ base s, CalleeUnwOkG
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K
      (fun _ => False) s (CallAt fa base) X XR U vcp.CallSite (fun _ _ => False))
    (hX : ∀ s, XCallsOk env.toEnv (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env.toEnv (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXR : ∀ s, XRaiseOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hXRi : ∀ s, XRaiseIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X XR)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {lsda : Option (List CallSite)} (hsites : callSites af fa = .ok lsda)
    (hlsda : T.lsda = lsda.map (List.map (·.entry)))
    {rows : List (Nat × Cfi)} (hrows : unwindRows af fa = .ok rows) (hcie : T.cie = cieInsns)
    (hfde : T.fde = insnsFrom 0 rows)
    (hpad : padsNonzeroB af fa = true) (_hlast : lastCallsOk af fa = true)
    (hsaved : savedCheck vcp rf = true)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitX env p cs) (fuel : Nat) :
    ArmRefinesU fb base ra (Unw.ArmStepU X H U T fa) s (Clif.runLoopX env p fuel cs.toX) :=
  backend_correct_final_cleanup_unwind_any hsub hc hlU hcov hC hCT hTls hU hX hXI hXR hXRi hsym
    hslot hsites hlsda hrows hcie hfde hpad hsaved hent hres hbe hargs hcs hrel htr fuel

end E2E
