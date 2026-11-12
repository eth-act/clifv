import FV.Link.Exe
import FV.E2E.ExecTlsProven

/-! # The executable compiler is correct, TLS included (T1)

`compileExe_correct_tls` (`_depth`, `_peak`): `compileExe_correct` (`_depth`, `_peak`) for the
hook-free executable machine `stepT` (`FV/E2E/ExecTls.lean`): every word of the program runs on
the processor, the local-exec TLS words `leanLink` writes included; only calls of code outside
the program are hooks. The TLS hook's trusted contract is replaced by the loader's
thread-pointer contract `TlsLoader`; `BaseOk` is of the base environment `leBase` (its TLS clause
holds, `tlsOk_le`) and `HooksSim` only covers the calls of code outside the program.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes Backend LinkSpec

/-- **The executable compiler is correct, TLS included** (T1): `compileExe_correct` for the
hook-free machine `stepT`, under the loader's thread-pointer contract `TlsLoader`. -/
theorem compileExe_correct_tls {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input (leBase S.input B file)))
    (hHc : ∀ d m e, Sim S.input m e → Sim S.input (B.hooks.call d m) (B.hooks.call d e))
    {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f (StackBound.stackFn S.input f) r
      args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs)
    (hL : TlsLoader S.input B file r) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (stepT S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_proven_tls (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hHc hf hc M hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr htr hL

/-- **`compileExe_correct_depth` without the TLS hook** (recursive programs; the stack
`frameDrop + (D * M + pbMax)`, #581). -/
theorem compileExe_correct_depth_tls {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input (leBase S.input B file)))
    (hHc : ∀ d m e, Sim S.input m e → Sim S.input (B.hooks.call d m) (B.hooks.call d e))
    {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f
      (frameDrop (art S.input f).af + (S.input.D * M + pbMax S.input)) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs)
    (hL : TlsLoader S.input B file r) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (stepT S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_depth_proven_tls (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hHc hf M hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr htr hL

/-- **`compileExe_correct_peak` without the TLS hook** (the stack `frameDrop + (D * d + pbMax)` for the
run's peak call depth `d`). -/
theorem compileExe_correct_peak_tls {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input (leBase S.input B file)))
    (hHc : ∀ d m e, Sim S.input m e → Sim S.input (B.hooks.call d m) (B.hooks.call d e))
    {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f
      (frameDrop (art S.input f).af + (S.input.D * d + pbMax S.input)) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.input) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs)
    (hL : TlsLoader S.input B file r) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (stepT S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (F + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_peak_proven_tls (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hHc hf F d hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr hd htr hL

end Link
