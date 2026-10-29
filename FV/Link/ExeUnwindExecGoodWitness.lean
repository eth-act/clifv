import FV.Link.ExeUnwindExecGood
import FV.Link.ExeUnwindExecWitness

/-!
# Witness: the executable-bytes theorems with unwinding apply without `RunOkU` (S10g, #404)

On the `%rec` executables of `FV/Link/ExeUnwindWitness.lean` (`compileExeU`) and
`FV/Link/OptExeUnwindWitness.lean` (`compileExeOptU`), with the closed base environment (whose
hooks meet `HooksSim`, `hooksSim_closed`): `compileExe_correct_unwind_exec_peak` and
`compileExeOpt_correct_unwind_exec_peak` instantiated at the written executables and `%rec`
(open: the premises about the base environment's `BaseOk`, the linked program's `BaseU`/`OkUNI`
and the entry).
-/

namespace Link.DeadCleanup.UnwindExecGoodWitness

open E2E E2E.LinkCheck E2E.BinCheck E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  Backend.Proof UnwindWitness UnwindExecWitness

/-- **`compileExe_correct_unwind_exec_peak` applies to `file`** with the closed base environment
(open: the premises about the base environment, the entry and the run). -/
theorem exec_applies (hB : BaseOk (sys spec.inputCleanup closedBase)) (Fu d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall spec.inputCleanup (BinCheck.roByte spec.inputCleanup spec.data) f
      (frameDrop (art spec.inputCleanup f).af + (spec.inputCleanup.D * d + pbMax spec.inputCleanup))
      r args cs.mem)
    (hr : ClifRun spec.inputCleanup closedBase f r args cs)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup spec.inputCleanup closedBase
      (worldF spec.inputCleanup f (spec.inputCleanup.D * d + pbMax spec.inputCleanup) r))
    (hb : BaseU L) (hNI : L.OkUNI) (hUS : UnwSim spec.inputCleanup L.Ub)
    (hra1 : ¬ img spec.inputCleanup (xreg 30 r - 1))
    (hd : Clif.DepthLeX L.envX L.P d cs.toX)
    (htr : TrapsExplicitX ((L.peakX Fu).envRX d f) L.P.bare cs) :
    ExecRefinesU (art spec.inputCleanup f).fb (art spec.inputCleanup f).base (xreg 30 r)
      (stepU spec.inputCleanup closedBase L.Ub file) r
      (DeadCleanupBinCheck.RelocAt spec.inputCleanup)
      (Clif.runLoopX L.envX L.P (Fu + 1) cs.toX) :=
  compileExe_correct_unwind_exec_peak compile_eq closedBase hB (hooksSim_closed _) f_eq Fu d hX ho
    hr L hLs hb hNI hUS hra1 hd htr

/-- **`compileExeOpt_correct_unwind_exec_peak` applies to the optimising compiler's `file`**
with the closed base environment (open as `exec_applies`). -/
theorem opt_exec_applies
    (hB : BaseOk (sys OptUnwindWitness.specO.opt.inputCleanup closedBase))
    (d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf OptUnwindWitness.file).Intact r)
    (ho : OutsideCall OptUnwindWitness.specO.opt.inputCleanup
      (BinCheck.roByte OptUnwindWitness.specO.opt.inputCleanup OptUnwindWitness.specO.opt.data)
      OptUnwindWitness.f' (frameDrop (art OptUnwindWitness.specO.opt.inputCleanup
        OptUnwindWitness.f').af + (OptUnwindWitness.specO.opt.inputCleanup.D * d +
          pbMax OptUnwindWitness.specO.opt.inputCleanup)) r args cs'.mem)
    (hr : ClifRun OptUnwindWitness.specO.opt.inputCleanup closedBase OptUnwindWitness.f' r args cs')
    (hcs : ClifEntry OptUnwindWitness.f args cs)
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup
      OptUnwindWitness.specO.opt.inputCleanup closedBase
      (worldF OptUnwindWitness.specO.opt.inputCleanup
        OptUnwindWitness.f' (OptUnwindWitness.specO.opt.inputCleanup.D * d +
          pbMax OptUnwindWitness.specO.opt.inputCleanup) r))
    (hb : BaseU L) (hNI : L.OkUNI) (hkeep : Opt.EnvKeepsSymbolsX L.envX)
    (hUS : UnwSim OptUnwindWitness.specO.opt.inputCleanup L.Ub)
    (hra1 : ¬ img OptUnwindWitness.specO.opt.inputCleanup (xreg 30 r - 1))
    (hd : Clif.DepthLeX L.envX L.P d cs'.toX)
    (htr : ∀ Fu, TrapsExplicitX ((L.peakX Fu).envRX d OptUnwindWitness.f') L.P.bare cs')
    (k : Nat) :
    ExecRefinesU (art OptUnwindWitness.specO.opt.inputCleanup OptUnwindWitness.f').fb
      (art OptUnwindWitness.specO.opt.inputCleanup OptUnwindWitness.f').base (xreg 30 r)
      (stepU OptUnwindWitness.specO.opt.inputCleanup closedBase L.Ub OptUnwindWitness.file) r
      (DeadCleanupBinCheck.RelocAt OptUnwindWitness.specO.opt.inputCleanup)
      (Clif.runLoopX L.envX (prog OptUnwindWitness.specO.inputCleanup) k cs.toX) :=
  compileExeOpt_correct_unwind_exec_peak OptUnwindWitness.compile_eq closedBase hB
    (hooksSim_closed _) OptUnwindWitness.f_eq OptUnwindWitness.f'_eq d hX ho hr hcs hregs hsl hmem
    L hLs hb hNI hkeep hUS hra1 hd htr k

/-- The raising base callees of a linked program without them meet `UnwSim`. -/
example : UnwSim spec.inputCleanup Unw.UnwHooks.none := unwSim_none _

/-- The closed base environment meets `BaseOk` for `%rec`'s input (no TLS). -/
theorem base_ok : BaseOk (sys spec.inputCleanup closedBase) := by
  refine baseOk_closedCleanup fun g hg => ?_
  have h : ((progOf spec.inputCleanup.resultsCleanup).funcs.all fun g => !hasTls g) = true := by
    native_decide
  simpa using List.all_eq_true.1 h g hg

/-- The closed base environment meets `BaseOk` for the optimised `%rec` input (no TLS). -/
theorem base_okO : BaseOk (sys OptUnwindWitness.specO.opt.inputCleanup closedBase) := by
  refine baseOk_closedCleanup fun g hg => ?_
  have h : ((progOf OptUnwindWitness.specO.opt.inputCleanup.resultsCleanup).funcs.all
      fun g => !hasTls g) = true := by
    native_decide
  simpa using List.all_eq_true.1 h g hg

/-- `exec_applies` with `BaseOk` discharged. -/
example := @exec_applies base_ok

/-- `opt_exec_applies` with `BaseOk` discharged. -/
example := @opt_exec_applies base_okO

end Link.DeadCleanup.UnwindExecGoodWitness
