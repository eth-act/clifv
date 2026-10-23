import FV.Link.DeadCleanupExeT
import FV.Link.ExeInputReachCleanupIn

/-! # The shipped executable compiler with the typed scope (S11, #35)

`Link.DeadCleanup.compileExeT`: on an input in `InScopeP` it is `compileExe` (`compileExeT_eq`);
otherwise it checks the typed input conditions `InScopePT`, runs the Lean linker `leanLink`, and
accepts its output only when the decided output checks `OutOkTCleanup` hold. Correctness:
`compileExeT_correct` (`compileExe_correct` on `InScopeP`, `compileExe_correctT` otherwise,
returned values by class: `ExecRefinesT`). Totality on `InScopeIn`:
`compileExeT_total_reach_input` (`compileExe_total_reach_input`). Used by `lean-link` without
`--verified`; `--verified` stays on `compileExe` (integer-only: its claim reaches the Rust
source through the integer front-end theorems).
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend LinkSpec

/-- The error on a typed input whose `leanLink` output fails `OutOkTCleanup`. -/
def outOkTMsg : String := "the typed input's compiled code fails the output checks (OutOkTCleanup)"

/-- The error on an input outside `InScopeP` and `InScopePT`. -/
def outOfScopeTMsg : String := "the input is outside the verified subset (InScopeP, InScopePT)"

/-- **The executable compiler with the typed scope**: `compileExe` on `InScopeP`; on
`InScopePT` the Lean linker followed by the output checks `OutOkTCleanup`. -/
def compileExeT (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  if inScopePar S.input0 then leanLink S file0
  else if InScopePT S.input0 then
    match leanLink S file0 with
    | .ok file => if OutOkTCleanup S.inputCleanup then .ok file else .error outOkTMsg
    | .error e => .error e
  else .error outOfScopeTMsg

/-- `InScopePT` reads the program and the CLIF image's symbols, not the depth. -/
theorem inScopePT_input (S : LinkSpec) : InScopePT S.inputCleanup = InScopePT S.input0 := rfl

/-- **`compileExeT` is `compileExe` on `InScopeP`**. -/
theorem compileExeT_eq {S : LinkSpec} (hin : InScopeP S.input0 = true) (file0 : ByteArray) :
    compileExeT S file0 = compileExe S file0 := by
  have hp : inScopePar S.input0 = true := by rw [inScopePar_eq]; exact hin
  simp only [compileExeT, compileExe, hp, if_true]

/-- `compileExeT`'s success: `compileExe`'s, or the typed premises of `compileExe_correctT`. -/
theorem compileExeT_spec {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT S file0 = .ok file) :
    compileExe S file0 = .ok file ∨
      (InScopePT S.inputCleanup = true ∧ OutOkTCleanup S.inputCleanup = true ∧
        leanLink S file0 = .ok file) := by
  unfold compileExeT at h
  split at h
  · rename_i hs
    left
    simp only [compileExe, hs, if_true]
    exact h
  · split at h
    · rename_i _ ht
      right
      split at h
      · rename_i file' hl
        split at h
        · rename_i ho
          cases h
          exact ⟨by rw [inScopePT_input]; exact ht, ho, hl⟩
        · cases h
      · cases h
    · cases h

/-- **The executable compiler with the typed scope is correct**: for `compileExeT S file0 = .ok
file` and an outside call of a function `f` of the program (no call cycle reachable from it), the
executable machine run of `file`'s own words refines the whole-program CLIF run, each returned
value in the ABI return register of its class (`ExecRefinesT`). -/
theorem compileExeT_correct {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs) :
    ExecRefinesT (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs) := by
  rcases compileExeT_spec h with hc0 | ⟨hin, hout, hl⟩
  · obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe hc0
    exact compileExe_correctT hin hout hl B hB hH hf hc M hX ho hr htr
  · exact compileExe_correctT hin hout hl B hB hH hf hc M hX ho hr htr

/-- **`compileExeT` succeeds on `InScopeIn`** (`compileExe_total_reach_input`). -/
theorem compileExeT_total_reach_input {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeIn (placed S).input0 = true) (hl : (placed S).layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : (placed S).file0OkB file0 phs = true)
    (hreach : (placed S).reachOkB = true) :
    compileExeT (placed S) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S) (tpOff phs))) := by
  rw [compileExeT_eq (inScopeP_of_input hin)]
  exact compileExe_total_reach_input hin hl hph hf hreach

end Link.DeadCleanup
