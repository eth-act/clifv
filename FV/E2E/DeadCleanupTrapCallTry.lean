import FV.E2E.DeadCleanupTrapCall
import FV.E2E.TrapCallTryPrep
import FV.E2E.RegLevelTrapCallTry

/-!
# The shipped compiler's per-function theorem with callee traps, `try_call`s included (S9b, #375)

`backend_correct_final_cleanup_trapcall` (S9a) needs a function without `try_call` terminators:
its proof device's exception would be caught by a `try_call`'s handler. Here the proof stops at
the trapping call instead of following the exception (`FV/E2E/TrapCallTryStop.lean`): the
CLIF → VCode simulation of the run up to the trapping step (`driver_trapStop`), `prune` and
`prepare` carrying a raising `tryCall` (`tryRaise_cleanup`), and the register level with the
semantics halting at a raising `tryCall` (`regLevel_trapCall_valueT`).

**`backend_correct_final_cleanup_trapcallT`**: the premises of
`backend_correct_final_cleanup_trapcall` without `∀ B ∈ f.blocks, B.term.isTry = false`, the run
premise `TrapsExplicitCT` (`TrapsExplicitC` without its `try_call` clauses: a trap of a
`try_call`'s callee allowed); conclusion: a trap site of `f`, or a callee-trap state at a call
site of either kind (`CallTrapAtT`), every earlier state `GoodX`. `TrapsExplicitC.toT`,
`CallTrapAt.toT`: the old theorem's runs and states are among the new one's.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.DeadCleanup

/-- **The shipped compiler's per-function theorem with callee traps, `try_call` callees
included**: for a function `f` compiled through the dead cleanup, in a program without functions
(`p.funcs = []`), whose lowering passes the unwinding validator (`lowerCheckU`), under the
premises of `backend_correct_final_cleanup` plus the trapping callees' contract (`XTrapsOk`), a
run of `f` that traps with `c` under `TrapsExplicitCT` (explicit traps and traps inside the
callees of `call`, `call_indirect`, `try_call` and `try_call_indirect`) is matched by the machine
run from the ABI entry: it reaches a trap site of `f` with code `c`, or a callee-trap state
(`CallTrapAtT` with `TrapCallSem … c`: the pc at a call or `try_call` of `f` whose callee traps
with `c`, the callee contract's premises holding there), every earlier state of the activation
`GoodX`. -/
theorem backend_correct_final_cleanup_trapcallT {p : Clif.Program} {f : Clif.Function} {k : Nat}
    {vc vcp : VCode} {rf : RFunc} {af : AFunc} {fa : FnAsm} {fb : FnBin}
    (hsub : InSubset p f) (hc : CompiledCleanupA f k vc vcp rf af fa fb)
    (hlU : lowerCheckU f vc = true) (hp : p.funcs = [])
    {X : ExtSem} {H : ArmHooks} {syms : String → Option Nat} {slotOff : Nat} {env : Clif.Env}
    {K : Nat}
    (hcov : FormsCovered ⟨fa.k, af.slotBase⟩ vcp)
    (hC : ∀ s, CalleeOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H vcp.CallSite)
    (hTls : hasTls f = true → ∀ s, TlsOk
      (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s) K X H)
    (hX : ∀ s, XCallsOk env (f.externs.map (·.2)) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXI : ∀ s, XCallsIndOk env (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hXT : ∀ s, XTrapsOk env (f.externs.map (·.2)) (indSigs f) (fun sl cm w =>
      Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s, syms,
        slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X)
    (hsym : ∀ n b, syms n = some b → X.sym n 0 = BitVec.ofNat 64 b)
    (hslot : af.slotBase = slotOff)
    {base ra : BitVec 64} {s w₀ : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hent : AbiEntry fb base ra s) (hres : StackAvail K af s) (hbe : BodyEntry af s w₀)
    (hargs : ArgsIn f.sig args s) (hcs : ClifEntry f args cs)
    (hrel : Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
      syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f cs.frame.slots cs.mem w₀)
    (htr : TrapsExplicitCT env p cs) {fuel : Nat} {c : Clif.TrapCode}
    (hrun : Clif.runLoop env p fuel cs = .trapped c) :
    ∃ n, TrapAt fb base c (runX (ArmStepX X H fa) n s) ∨
      (CallTrapAtT vcp (frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s)
          K (fun _ => False) s fa base X (fun _ _ => False)
          (TrapCallSem env (f.externs.map (·.2)) (indSigs f) (fun sl cm w =>
            Rel.holds ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
              syms, slotOff, (RAFrame.compute vcp rf).intBase⟩ f sl cm w) X c)
          (runX (ArmStepX X H fa) n s) ∧
        ∀ i < n, actGoodX vcp rf af fa fb base s X H K (fun _ => False) (fun _ _ => False)
          (runX (ArmStepX X H fa) i s)) := by
  let Γ : Rel := ⟨frameW K (RAFrame.compute vcp rf).intBase (RAFrame.compute vcp rf).size af s,
    syms, slotOff, (RAFrame.compute vcp rf).intBase⟩
  let XT := TrapCallSem env (f.externs.map (·.2)) (indSigs f) (fun sl cm w => Γ.holds f sl cm w) X c
  let fctx : FnCtx := ⟨fa.k, af.slotBase⟩
  have hexcl : ∀ d uses w, X.call d uses w ≠ none → (xrT XT).raise d uses w = none :=
    fun _ _ _ hne => xrT_none fun h => hne h.1
  have houtB := outgoing_le_intBaseCleanupA hc
  have hRef := refines_valueSemU Γ.F fctx X (xrT XT)
  have hMem := memRefines_valueSemU Γ.F fctx X (xrT XT) hslot hsym
  have hcallsR := callsRefine_valueSemU (F := Γ.F) (ctx := fctx) (xCallsOk_trapEnv (c := c) (hX s))
    hexcl
  have hicallsR := indCallsRefine_valueSemU (F := Γ.F) (ctx := fctx)
    (xCallsIndOk_trapEnv (c := c) (hXI s)) hsym (fun _ _ _ h => h.1.symbols) hexcl
  -- CLIF → VCode up to the trapping step, on the proof device `trapEnv env c`
  obtain ⟨ctx, st0, R, gn, bl, A, hshape, hcert, hbr, hUs⟩ := loweringU_of_check hlU
  have HD : DriverHyp f vc ctx st0 R gn bl A (valueSemU Γ.F fctx X (xrT XT))
      (fun sl cm w => Γ.holds f sl cm w) (trapEnv env c).toEnv p :=
    { shape := hshape
      cert := hcert
      dsem := (driverSem_valueSemU Γ.F fctx X (xrT XT)).toDriverSemG
      insts := instCalls_of_rules lowerRulesCorrect_program excludedUnmatchable callRulesCorrect
        indRulesCorrect memRulesCorrect_program hRef (mrStable_holds Γ f) hcallsR hicallsR hMem
        (outArgsOk_holds Γ f) (callsStack_mono (callsStack_of_check hc.lowerOk) houtB)
        (indStack_mono (indStack_of_check hc.lowerOk) houtB) (memRelOk_holds Γ f)
      terms := termCalls_of_rules lowerTermRulesCorrect termUnmatchable branchRulesCorrect
        branchExcludedUnmatchable hRef (mrStable_holds Γ f)
      ext := fun B hB st hst fn args hi e he => hsub.externCalls B hB st hst fn args hi e he
      indSig := indSig_of_subset hsub
      subE := hsub.subsetE
      entryLocs := entryOk_of_check hc.lowerOk
      brIdx := hbr
      noTail := noTail_of_subset hsub
      tries := ⟨Γ.out, tryCalls_of_rules tryRulesCorrect tryUnmatchable hRef (mrStable_holds Γ f)
        hMem (outArgsOk_holds Γ f) hcallsR, tryStack_mono (tryStack_of_check hc.lowerOk) houtB⟩
      tryExt := hsub.tryExterns
      tryInd := tryIndCalls_of_rules tryIndRulesCorrect tryIndUnmatchable hRef
        (mrStable_holds Γ f) hMem (outArgsOk_holds Γ f)
        (indStack_mono (indStack_of_check hc.lowerOk) houtB) hicallsR
      tryIndSig := tryIndSig_of_subset hsub
      cfg := by
        obtain ⟨ss, ps, he⟩ := cfg_of_prepare hc.prepare
        exact ⟨ss, ps, (prune_cfg vc).symm.trans he⟩ }
  have HR : RaiseHyp f (valueSemU Γ.F fctx X (xrT XT)) (fun sl cm w => Γ.holds f sl cm w)
      (trapEnv env c) Γ.F X (xrT XT) Γ.slotOff Γ.syms Γ.out :=
    ⟨raiseSem_valueSemU _ _ _ _, hRef, hMem, mrStable_holds Γ f, outArgsOk_holds Γ f,
      memRelOk_holds Γ f, callsStack_mono (callsStack_of_check hc.lowerOk) houtB,
      tryStack_mono (tryStack_of_check hc.lowerOk) houtB,
      indStack_mono (indStack_of_check hc.lowerOk) houtB, xRaiseOk_trapEnv (hXT s),
      xRaiseIndOk_trapEnv (hXT s), hsym, fun sl cm w h => (memRelOk_holds Γ f).symbols sl cm w h⟩
  -- the register level
  obtain ⟨ρ₀, hR1, hR2, hR3⟩ := regLevel_trapCall_valueT hc.check hc.alloc hc.emit hc.layout hcov hC
    (fun h => hTls (hasTls_of_vcodeCleanupA hc h)) XT hent hres hbe
  obtain ⟨B0, hentB, hbody, hterm, hty, hregs⟩ := hcs.entry
  have hB0 : f.blocks[0]? = some B0 := by
    simpa [Clif.Function.entry?, List.head?_eq_getElem?] using hentB
  have hargsE := argsAtEntry_body (lowerRFunc_frame hc.alloc) (entryRegs_of_check hc.lowerOk) hbe
    hargs (stackArgsAvoid_frameWCleanupA hc hres hent hargs)
  -- `prune` + `prepare`
  have hPrep := prepareCorrectU_cleanup_value hc Γ.F fctx X (xrT XT)
  rcases driver_trapStop (slots := cs.frame.slots) (ρ₀ := ρ₀) hp HD (hUs) HR
      (driverSem_valueSemU Γ.F fctx X (xrT XT)) hB0 hcs.callers hcs.func rfl hbody hterm hregs
      hty.symm hcs.sig hrel hargsE htr hrun with h | ⟨obj, w', h⟩ | h
  · exact hR1 c ((hPrep.1 _ _).2 c h)
  · obtain ⟨n, hn⟩ := hR2 obj w' (hPrep.2 _ _ _ _ h)
    exact ⟨n, .inr hn⟩
  · obtain ⟨n, hn⟩ := hR3 (tryRaise_cleanup (driverSem_valueSemU Γ.F fctx X (xrT XT))
      (fun _ _ _ _ _ _ hp' h' => valueSemU_pure hp' h') (valueSemU_cmpOverwrite _ _ _ _)
      hc.prepOk (xrT XT) h)
    exact ⟨n, .inr hn⟩

end E2E
