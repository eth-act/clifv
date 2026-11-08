import FV.Link.DeadCleanupExe
import FV.E2E.DeadCleanupExecPeak

/-! # The shipped executable compiler is correct for recursive programs (L1d)

`Link.DeadCleanup.compileExe` (the input conditions `InScopeP`, then the cleanup linker
`Link.DeadCleanup.leanLink`) is what `lake exe lean-link` and `cargo fv --lean-link` run by
default. `Link.DeadCleanup.compileExe_correct` covers an entry that reaches no call cycle;
**`compileExe_correct_peak`** covers any entry, recursive ones included, with
`frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)` bytes of
stack (#581: `pbMax`, the most bytes a function's stack probes write below its frame) for the CLIF run's
peak call depth `d` (`Clif.DepthLe`), as `Link.compileExe_correct_peak` for the baseline
compiler. It composes the cleanup chain's per-program facts (`okB_leanLink`, `binOk_leanLink`,
`codeMap_leanLink`, `gotOk_leanLink`, `outsideAvoids_leanLink`, `FV/Link/DeadCleanupExe.lean`)
with `E2E.DeadCleanupExecBytes.binary_correct_exec_peak_proven`.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  LinkSpec

/-- **The shipped executable compiler is correct for recursive programs, with the stack of the
run's peak call depth** (L1d): `compileExe_correct` without the call-graph premise. For
`compileExe S file0 = .ok file`, an outside call of a function `f` of the program with
`frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)` bytes of
stack (#581: with the stack probes of the deepest activation), where `d` bounds the
call depth of the whole-program CLIF run (`Clif.DepthLe`: every state the run from `cs` reaches
has at most `d` callers), the executable machine run of `file`'s own words refines the
whole-program CLIF run of at most `F + 1` steps (`ExecRefines`; `TrapsExplicit` under
`Clif.linkEnvD`). -/
theorem compileExe_correct_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
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
    ExecRefines (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact binary_correct_exec_peak_proven (okB_leanLink hin hl)
    (codeMap_leanLink hl) (binOk_leanLink hl) (gotOk_leanLink hl) B hB hH hf F d hX ho
    (outsideAvoids_leanLink hl _ _ _ _ _) hr hd htr

end Link.DeadCleanup
