import FV.Link.DeadCleanupExe
import FV.E2E.DeadCleanupBinaryInitTR

/-!
# The executable compiler under the slot-byte oracle, corrected premises (SEM1 #537, #719, #716)

**`compileExe_correct_initR`**: `compileExe_correct_init` with the oracle route's corrected
premises `InitOkR` (`DetPRBR` for the false `DetPRB`, #719; the call twins `CallTwinCE` for
`DetTabPRBE`/`DetTabPRBr`, #716) in place of `InitOk`. **`compileExe_correct_initTR`**: the same
for a trapping whole-program CLIF run whose traps are explicit (`TrapsExplicit`, as
`compileExe_correct`): the executable's run reaches the trap site.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend LinkSpec

/-- **The executable compiler is correct under the slot-byte oracle, returning runs, corrected
premises** (module doc). -/
theorem compileExe_correct_initR {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRunB S.inputCleanup B M f r args cs)
    (hIO : InitOkR (sysS S.inputCleanup B f r (GotSlot S.inputCleanup file))
      (kapW S.inputCleanup B f r))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs = .returned vals cm) :
    ExecRefines (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (.returned vals cm) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_initR (okB_leanLink hin hl) (codeMap_leanLink hl) (binOk_leanLink hl)
    (gotOk_leanLink hl) B hB hH hf hc M hX ho (outsideAvoids_leanLink hl _ _ _ _ _) hr hIO hrun

/-- **The executable compiler is correct under the slot-byte oracle, trapping runs, corrected
premises** (module doc). -/
theorem compileExe_correct_initTR {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRunB S.inputCleanup B M f r args cs)
    (hIO : InitOkR (sysS S.inputCleanup B f r (GotSlot S.inputCleanup file))
      (kapW S.inputCleanup B f r))
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs)
    {c : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs = .trapped c) :
    ExecRefines (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (.trapped c) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_initTR (okB_leanLink hin hl) (codeMap_leanLink hl) (binOk_leanLink hl)
    (gotOk_leanLink hl) B hB hH hf hc M hX ho (outsideAvoids_leanLink hl _ _ _ _ _) hr hIO htr hrun

end Link.DeadCleanup
