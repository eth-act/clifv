import FV.Link.DeadCleanupExe
import FV.E2E.DeadCleanupBinaryInitRC

/-!
# The executable compiler under the slot-byte oracle on decidable checks (SEM1 #537, #713, #733)

**`compileExe_correct_initRC`**, **`compileExe_correct_initRCT`**: `compileExe_correct_initRU` /
`compileExe_correct_initTRU` without `InitOkRU`. Their premises besides those of
`compileExe_correct` are

* one decidable check of the compiled program, `(sys S.inputCleanup B).initChecksB = true`
  (`LinkSys.initChecksB`: per function `retCountB` (`RetCount`, #733), `FnAsm.x30Free`,
  `VCode.retsLow`, `FnAsm.blrLow`, `slotsNIB`; it reads only the program and its compilation);
* the base environment's `BaseRetOk` (returning externs keep the valid addresses and the symbols)
  and `HooksKeep` (the hooks keep an error state and the loaded program);
* the trusted base-hook fact `BaseNIX` (#704: the hooks do not observe the exterior of a machine
  entry), of the proof's system.

The closed base satisfies the three base conditions (`baseRetOk_closedSys`, `hooksKeep_closedSys`,
`baseNIX_closed`).
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  LinkSpec

/-- **The executable compiler is correct under the slot-byte oracle, returning runs, decidable
checks** (module doc). -/
theorem compileExe_correct_initRC {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRunB S.inputCleanup B M f r args cs)
    (hchk : (sys S.inputCleanup B).initChecksB = true)
    (hBR : (sys S.inputCleanup B).BaseRetOk) (hK : (sys S.inputCleanup B).HooksKeep)
    (hNX : (sysS S.inputCleanup B f r (GotSlot S.inputCleanup file)).BaseNIX)
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs = .returned vals cm) :
    ExecRefines (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (.returned vals cm) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_initRC (okB_leanLink hin hl) (codeMap_leanLink hl) (binOk_leanLink hl)
    (gotOk_leanLink hl) B hB hH hf hc M hX ho (outsideAvoids_leanLink hl _ _ _ _ _) hr hchk hBR
    hK hNX hrun

/-- **The executable compiler is correct under the slot-byte oracle, trapping runs, decidable
checks** (module doc). -/
theorem compileExe_correct_initRCT {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRunB S.inputCleanup B M f r args cs)
    (hchk : (sys S.inputCleanup B).initChecksB = true)
    (hBR : (sys S.inputCleanup B).BaseRetOk) (hK : (sys S.inputCleanup B).HooksKeep)
    (hNX : (sysS S.inputCleanup B f r (GotSlot S.inputCleanup file)).BaseNIX)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs)
    {c : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs = .trapped c) :
    ExecRefines (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (.trapped c) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_initTRC (okB_leanLink hin hl) (codeMap_leanLink hl) (binOk_leanLink hl)
    (gotOk_leanLink hl) B hB hH hf hc M hX ho (outsideAvoids_leanLink hl _ _ _ _ _) hr hchk hBR
    hK hNX htr hrun

end Link.DeadCleanup
