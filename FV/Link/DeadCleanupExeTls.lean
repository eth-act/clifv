import FV.Link.DeadCleanupExePeak
import FV.E2E.DeadCleanupExecTlsProven

/-! # The shipped executable compiler is correct, TLS included (T1)

`compileExe_correct_tls` (`_peak`): `Link.DeadCleanup.compileExe_correct` (`_peak`) for the
hook-free executable machine `stepT` of the cleanup input (`FV/E2E/DeadCleanupExecTls.lean`):
every word of the program runs on the processor, the local-exec TLS words the cleanup linker
writes included; only calls of code outside the program are hooks. The TLS hook's trusted
contract is replaced by the loader's thread-pointer contract `TlsLoader`; `BaseOk` is of the base
environment `leBase` (its TLS clause holds, `tlsOk_le`) and `HooksSim` only covers the calls of
code outside the program. `Link.compileExe_correct_tls` (`FV/Link/ExeTls.lean`) is the baseline
compiler's.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  LinkSpec

/-- **The shipped executable compiler is correct, TLS included** (T1): `compileExe_correct` for
the hook-free machine `stepT`, under the loader's thread-pointer contract `TlsLoader`. -/
theorem compileExe_correct_tls {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys S.inputCleanup (leBase S.inputCleanup B file)))
    (hHc : ∀ d m e, Sim S.inputCleanup m e →
      Sim S.inputCleanup (B.hooks.call d m) (B.hooks.call d e))
    {n : String} {f : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M)
      (prog S.inputCleanup).bare cs)
    (hL : TlsLoader S.inputCleanup B file r) :
    ExecRefines (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (stepT S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_proven_tls (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hHc hf hc M hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr htr hL

/-- **`compileExe_correct_peak` without the TLS hook** (recursive programs; the stack
`frameDrop + D * d` for the run's peak call depth `d`). -/
theorem compileExe_correct_peak_tls {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys S.inputCleanup (leBase S.inputCleanup B file)))
    (hHc : ∀ d m e, Sim S.inputCleanup m e →
      Sim S.inputCleanup (B.hooks.call d m) (B.hooks.call d e))
    {n : String} {f : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (frameDrop (art S.inputCleanup f).af + S.inputCleanup.D * d) r args cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.inputCleanup) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
      (prog S.inputCleanup).bare cs)
    (hL : TlsLoader S.inputCleanup B file r) :
    ExecRefines (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (stepT S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_peak_proven_tls (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hHc hf F d hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr hd htr hL

end Link.DeadCleanup
