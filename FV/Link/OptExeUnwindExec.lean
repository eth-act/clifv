import FV.Link.OptExeUnwind
import FV.Link.ExeUnwindExec

/-!
# The optimising executable compiler on the exceptional edges, on the executable's bytes (S10g)

`compileExeOpt_correct_unwind_peak` (`FV/Link/OptExeUnwind.lean`) on the executable machine with
unwinding (`E2E.DeadCleanupExecBytes.stepU`, `FV/E2E/DeadCleanupExecUnwind.lean`):
**`compileExeOpt_correct_unwind_exec_peak_of_good`** — for `compileExeOptU S file0 = .ok file`, an
outside call of the compiled optimised function `f'` in `r` (`compileExeOpt_correct_peak`'s
premises) and the linked program with unwinding of the optimised input with that call's world,
the executable machine with unwinding run from `r` refines every run with unwinding of the
input's program from the entry of its function `f` named as `f'` with the call's registers, slots
and memory (`ExecRefinesU`): the mid-end's simulation with handler edges
(`Opt.runLoopX_refinesU`) matches each outcome by the optimised run's, and
`compileExe_correct_unwind_exec_peak_of_good` at that run's fuel closes the chain. Open, as there:
the per-state facts `RunOkU` of the model's run.
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  Backend.Proof LinkSpec

theorem execRefinesU_of_outcome {fb : FnBin} {base ra : BitVec 64}
    {step : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {R : BitVec 64 → Prop}
    {o o' : Clif.XOutcome} (h : Opt.XOutcomeRefines o o')
    (hA : ExecRefinesU fb base ra step s R o') : ExecRefinesU fb base ra step s R o := by
  obtain ⟨hret, htrap, hunw⟩ := h
  cases hrn : o with
  | returned vals m => rw [hret vals m hrn] at hA; exact hA
  | trapped c => rw [htrap c hrn] at hA; exact hA
  | unwound e m => rw [hunw e m hrn] at hA; exact hA
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **The optimising executable compiler is correct on the exceptional edges, through the
mid-end, on the executable's bytes, for the run's peak call depth** (given the per-state facts
`RunOkU` of the model's run): for `compileExeOptU S file0 = .ok file`, an outside call of the
optimised function `f'` (named `n`) in `r` with `frameDrop + (D * d + pbMax)` bytes of stack, the linked
program with unwinding `L` of the optimised input with that call's world (its CLIF environment
keeping the link-time symbols), the entry `cs` of the input's function `f` named `n` with the
call's registers, slots and memory, and a bound `d` on the call depth of the optimised program's
run with unwinding: for every fuel `k` the executable machine with unwinding run from `r` refines
the input program's run with unwinding of `k` steps from `cs` (`ExecRefinesU`). -/
theorem compileExeOpt_correct_unwind_exec_peak_of_good {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOptU S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys S.opt.inputCleanup B)) {n : String} {f f' : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f') (d : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs cs' : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (frameDrop (art S.opt.inputCleanup f').af + (S.opt.inputCleanup.D * d + pbMax S.opt.inputCleanup))
      r args cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args cs') (hcs : ClifEntry f args cs)
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.opt.inputCleanup B
      (worldF S.opt.inputCleanup f' (S.opt.inputCleanup.D * d + pbMax S.opt.inputCleanup) r))
    (hb : BaseU L) (hNI : L.OkUNI) (hkeep : Opt.EnvKeepsSymbolsX L.envX)
    (hUS : UnwSim S.opt.inputCleanup L.Ub) (hra1 : ¬ img S.opt.inputCleanup (xreg 30 r - 1))
    (hd : Clif.DepthLeX L.envX L.P d cs'.toX)
    (htr : ∀ Fu, TrapsExplicitX ((L.peakX Fu).envRX d f') L.P.bare cs')
    (hrun : RunOkU S.opt.inputCleanup B file L d f' (modelOf S.opt.inputCleanup f' r))
    (k : Nat) :
    ExecRefinesU (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
      (stepU S.opt.inputCleanup B L.Ub file) r (DeadCleanupBinCheck.RelocAt S.opt.inputCleanup)
      (Clif.runLoopX L.envX (prog S.inputCleanup) k cs.toX) := by
  have hP : L.P = prog S.opt.inputCleanup := by rw [hLs]; rfl
  have hpair : Opt.FunSimU f f' := by
    obtain ⟨g, hg, hfg⟩ := ((funsSimU_prog S).findP (· == n)).1 f hf
    have : (prog S.opt.inputCleanup).func? n = some g := hg
    rw [hf'] at this
    cases this
    exact hfg
  obtain ⟨m, hm⟩ := Opt.runLoopX_refinesU hkeep (funsSimU_prog S) k cs.toX cs'.toX
    (sru_entry hpair hcs hr.entry hregs hsl hmem)
  have hpk := fun Fu => compileExe_correct_unwind_exec_peak_of_good h B hB hf' Fu d hX ho hr L hLs
    hb hNI hUS hra1 hd (htr Fu) hrun
  rw [← hP] at hm
  cases m with
  | zero =>
    refine execRefinesU_of_outcome hm ?_
    rw [Clif.runLoopX]
    trivial
  | succ Fu => exact execRefinesU_of_outcome hm (hpk Fu)

end Link.DeadCleanup
