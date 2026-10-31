import FV.Link.DeadCleanupExe
import FV.E2E.SretReturnLink

/-!
# The executable compiler with the `sret` return register (S7)

`compileExe_correct_abi`: `compileExe_correct` for an outside-called function whose `sret` value
is bound once (`sretStableB f`, the per-function check `lean-e2e-check` reports), and a return of
the executable machine also leaves the ABI return values `sretArg f args` after the CLIF results,
in x8 (`ExecRefinesAbi`; for a function with an `sret` parameter `i` and no returns, `args[i]`
in x8; until #587: in x0, as the backend moved the pointer there).
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  LinkSpec
open Backend.Proof.Driver (sretStableB)

/-- **The executable compiler is correct, with the ABI return values**: `compileExe_correct`
(its premises plus `sretStableB f`), and a return also leaves `sretArg f args` after the CLIF
results, in x8 (`ExecRefinesAbi`, restated for #587). -/
theorem compileExe_correct_abi {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f) (hS : sretStableB f = true)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M)
      (prog S.inputCleanup).bare cs) :
    ExecRefinesAbi (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (sretArg f args) (Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_proven_abi (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hH hf hS hc M hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr htr

end Link.DeadCleanup
