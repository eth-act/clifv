import FV.Link.DeadCleanupCompileT
import FV.E2E.DeadCleanupExecPeakT

/-! # The shipped executable compiler on the typed scope at the run's peak call depth (L1d)

`Link.DeadCleanup.compileExeT` is what `lake exe lean-link` runs without `--verified`: it checks
the typed input conditions `InScopePT` (the typed scope: float data movement, float parameters
and returns), runs the Lean linker and accepts its output only when the decided output checks
`OutOkTCleanup` hold (`FV/Link/DeadCleanupCompileT.lean`).

**`compileExe_correct_peakT`** is `Link.DeadCleanup.compileExe_correct_peak` on the typed input
conditions: for `leanLink S file0 = .ok file` on a typed in-scope input passing the output
checks, an outside call of a function `f` of the program with
`frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)` bytes of stack (#581), where `d` bounds the
call depth of the whole-program CLIF run (`Clif.DepthLe`), the executable machine run of `file`'s
own words refines the whole-program CLIF run of at most `F + 1` steps (`ExecRefinesT`;
`TrapsExplicit` under `Clif.linkEnvD`). It composes the typed cleanup facts of `leanLink`'s
output (`okBT_leanLink`, `codeMap_leanLink`, `binOk_leanLink`, `gotOk_leanLink`,
`outsideAvoids_leanLink`, `FV/Link/DeadCleanupExeT.lean`) with
`E2E.DeadCleanupExecBytes.binary_correct_exec_peak_provenT`.

**`compileExeT_correct_peak`** is the same for the shipped compiler with the typed scope
`compileExeT` (`compileExeT_eq` on `InScopeP`, the typed branch otherwise; by cases on
`compileExeT_spec`, through `typedPremises_of_compileExe` in the integer case), as
`Link.DeadCleanup.compileExeT_correct` for the non-peak theorem.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  LinkSpec

/-- **The shipped executable compiler is correct on the typed scope at the run's peak call
depth** (L1d; `Link.DeadCleanup.compileExe_correct_peak` for `InScopeP`): for `leanLink S file0 =
.ok file` on a typed in-scope input passing the output checks, an outside call of a function `f`
of the program with `frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)` bytes of stack,
where `d` bounds the call depth of the whole-program CLIF run (`Clif.DepthLe`: every state the
run from `cs` reaches has at most `d` callers), the executable machine run of `file`'s own words
refines the whole-program CLIF run of at most `F + 1` steps, each returned value in the ABI
return register of its class (`ExecRefinesT`; `TrapsExplicit` under `Clif.linkEnvD`). -/
theorem compileExe_correct_peakT {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopePT S.inputCleanup = true) (hout : OutOkTCleanup S.inputCleanup = true)
    (h : leanLink S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args
      cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.inputCleanup) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
      (prog S.inputCleanup).bare cs) :
    ExecRefinesT (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs) :=
  binary_correct_exec_peak_provenT (okBT_leanLink hin hout h)
    (codeMap_leanLink h) (binOk_leanLink h) (gotOk_leanLink h) B hB hH hf F d hX ho
    (outsideAvoids_leanLink h _ _ _ _ _) hr hd htr

/-- **The shipped executable compiler with the typed scope is correct at the run's peak call
depth** (L1d; `Link.DeadCleanup.compileExeT_correct` without the depth premise): for
`compileExeT S file0 = .ok file` — `compileExe` on `InScopeP`, else the Lean linker followed by
the output checks on a typed in-scope input — and an outside call of a function `f` of the
program with `frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)` bytes of stack, where
`d` bounds the call depth of the whole-program CLIF run (`Clif.DepthLe`), the executable machine
run of `file`'s own words refines the whole-program CLIF run of at most `F + 1` steps
(`ExecRefinesT`; `TrapsExplicit` under `Clif.linkEnvD`). -/
theorem compileExeT_correct_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args
      cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.inputCleanup) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
      (prog S.inputCleanup).bare cs) :
    ExecRefinesT (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs) := by
  rcases compileExeT_spec h with hc0 | ⟨hin, hout, hl⟩ | ⟨hI, hl⟩
  · obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe hc0
    exact compileExe_correct_peakT hin hout hl B hB hH hf F d hX ho hr hd htr
  · exact compileExe_correct_peakT hin hout hl B hB hH hf F d hX ho hr hd htr
  · exact binary_correct_exec_peak_provenT hI (codeMap_leanLink hl) (binOk_leanLink hl)
      (gotOk_leanLink hl) B hB hH hf F d hX ho (outsideAvoids_leanLink hl _ _ _ _ _) hr hd htr

end Link.DeadCleanup
