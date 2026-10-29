module

public import FV.Link.DeadCleanupExe
public import FV.E2E.DeadCleanupBinaryInit

@[expose] public section

/-!
# The executable compiler under the slot-byte oracle (SEM1 #537, executable level (c))

`compileExe_correct` (`DeadCleanupExe`) relates the executable run to the whole-program CLIF run
from a reference entry (`ClifRun`) without slot-byte oracle: with a slotted program callee a
CLIF run that reads an unwritten stack-slot byte is stuck there and the theorem says nothing
(#537). **`compileExe_correct_init`**: the same for a reference entry placed with the machine's
own slot table (`ClifRunB`, `binary_correct_exec_init`), for **returning** CLIF runs; premises
beside `compileExe_correct`'s: the oracle route's `InitOk` (scope conditions `BaseRetOk`,
`RetCount`, `HooksKeep`; determinism `DetPRB`, `DetTabPRBE`, `DetTabPRBr`, #701/#713) for the
system keeping the GOT slots. A trapping CLIF run under the oracle is not covered by any theorem
yet.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend LinkSpec

/-- **The executable compiler is correct under the slot-byte oracle, returning runs** (module
doc): for `compileExe S file0 = .ok file` and an outside call of a function `f` of the program (no
call cycle reachable from it), the executable machine run of `file`'s own words from `r` refines a
returning whole-program CLIF run from the reference entry placed with the machine's own slot
table. -/
theorem compileExe_correct_init {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRunB S.inputCleanup B M f r args cs)
    (hIO : InitOk (sysS S.inputCleanup B f r (GotSlot S.inputCleanup file))
      (kapW S.inputCleanup B f r))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs = .returned vals cm) :
    ExecRefines (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (.returned vals cm) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_init (okB_leanLink hin hl) (codeMap_leanLink hl) (binOk_leanLink hl)
    (gotOk_leanLink hl) B hB hH hf hc M hX ho (outsideAvoids_leanLink hl _ _ _ _ _) hr hIO hrun

end Link.DeadCleanup
