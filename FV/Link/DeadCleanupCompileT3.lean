module

public import FV.Link.DeadCleanupCompileT
public import FV.E2E.LinkScopeInputT3

@[expose] public section

/-! # The shipped executable compiler with the decider-free typed scope (S11, #35)

`Link.DeadCleanup.compileExeT3` is `compileExeT` with the typed branch's input check
`InScopePT` (which runs `lowerFunction` per function, `lowersTB`) replaced by the decided input
conditions `InScopeInT3` (no conjunct runs the compiler). `InScopeInT3` is inside `InScopePT`
(`LinkCheck.inScopePT_of_inT3`), so the correctness is `compileExe_correctT`'s:
`compileExeT3_correct`. Totality on `InScopeIn`: `compileExeT3_total_reach_input`.
`compileExeT` and its theorems are unchanged.
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend LinkSpec

/-- The error on an input outside `InScopeP` and `InScopeInT3`. -/
def outOfScopeT3Msg : String := "the input is outside the verified subset (InScopeP, InScopeInT3)"

/-- **The executable compiler with the decider-free typed scope**: `compileExe` on `InScopeP`;
on `InScopeInT3` the Lean linker followed by the output checks `OutOkTCleanup`. -/
def compileExeT3 (S : LinkSpec) (file0 : ByteArray) : Except String ByteArray :=
  if inScopePar S.input0 then leanLink S file0
  else if InScopeInT3 S.input0 then
    match leanLink S file0 with
    | .ok file => if OutOkTCleanup S.inputCleanup then .ok file else .error outOkTMsg
    | .error e => .error e
  else .error outOfScopeT3Msg

/-- **`compileExeT3` is `compileExe` on `InScopeP`**. -/
theorem compileExeT3_eq {S : LinkSpec} (hin : InScopeP S.input0 = true) (file0 : ByteArray) :
    compileExeT3 S file0 = compileExe S file0 := by
  have hp : inScopePar S.input0 = true := by rw [inScopePar_eq]; exact hin
  simp only [compileExeT3, compileExe, hp, if_true]

/-- `compileExeT3`'s success: `compileExe`'s, or the typed premises of `compileExe_correctT`. -/
theorem compileExeT3_spec {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT3 S file0 = .ok file) :
    compileExe S file0 = .ok file ∨
      (InScopePT S.inputCleanup = true ∧ OutOkTCleanup S.inputCleanup = true ∧
        leanLink S file0 = .ok file) := by
  unfold compileExeT3 at h
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
          exact ⟨by rw [inScopePT_input]; exact inScopePT_of_inT3 ht, ho, hl⟩
        · cases h
      · cases h
    · cases h

/-- **The executable compiler with the decider-free typed scope is correct** (the statement of
`compileExeT_correct`). -/
theorem compileExeT3_correct {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT3 S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
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
  rcases compileExeT3_spec h with hc0 | ⟨hin, hout, hl⟩
  · obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe hc0
    exact compileExe_correctT hin hout hl B hB hH hf hc M hX ho hr htr
  · exact compileExe_correctT hin hout hl B hB hH hf hc M hX ho hr htr

/-- **`compileExeT3` succeeds on `InScopeIn`** (`compileExe_total_reach_input`). -/
theorem compileExeT3_total_reach_input {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeIn (placed S).input0 = true) (hl : (placed S).layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : (placed S).file0OkB file0 phs = true)
    (hreach : (placed S).reachOkB = true) :
    compileExeT3 (placed S) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S) (tpOff phs))) := by
  rw [compileExeT3_eq (inScopeP_of_input hin)]
  exact compileExe_total_reach_input hin hl hph hf hreach

end Link.DeadCleanup
