import FV.Link.ReturnPinCompilerKernel
import FV.Link.Exe
import FV.Link.ReturnPinCompileDefs
import FV.Link.ProductionImageWithProof
import FV.E2E.ReturnPinExecProven

namespace Link.ReturnPinCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes Backend
variable {lower : ProductionLowering}

abbrev input (lower : ProductionLowering) (S : LinkSpec) (cleanup : Bool) : SemanticStackBound.CompilerInput :=
  {toLinkInput := S.inputProductionWith lower cleanup,cleanup,lower}

theorem attempt_spec {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) :
    ReturnPinBinary.okB (input lower S cleanup) = true ∧
    leanLinkProductionWith lower S file0 cleanup = .ok file := by
  exact Link.ReturnPinCompilerFor.attempt_spec
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (S := S) (cleanup := cleanup)
    (file0 := file0) (file := file) (h := h)

theorem codeMap_leanLink {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : leanLinkProductionWith lower S file0 cleanup = .ok file) :
    codeMapB (input lower S cleanup) (tabOf (input lower S cleanup).results) = true := by
  exact Link.ReturnPinCompilerFor.codeMap_leanLink
    (S := S) (cleanup := cleanup) (file0 := file0)
    (file := file) (h := h)

theorem leanLink_gotSlot {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : leanLinkProductionWith lower S file0 cleanup = .ok file) (a : BitVec 64) : ¬ GotSlot (input lower S cleanup) file a := by
  exact Link.ReturnPinCompilerFor.leanLink_gotSlot
    (S := S) (cleanup := cleanup) (file0 := file0)
    (file := file) (h := h) (a := a)

/-- **`GotOk` of `leanLink`'s output** (no GOT slot). -/
theorem gotOk_leanLink {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : leanLinkProductionWith lower S file0 cleanup = .ok file) : GotOk (input lower S cleanup) file := by
  exact Link.ReturnPinCompilerFor.gotOk_leanLink
    (S := S) (cleanup := cleanup) (file0 := file0)
    (file := file) (h := h)

/-- The outside caller avoids `leanLink`'s GOT slots (there is none). -/
theorem outsideAvoids_leanLink {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : leanLinkProductionWith lower S file0 cleanup = .ok file) (f : Clif.Function) (N : Nat) (r : Arm.ArmState)
    (args : List Clif.Val) (cm : Clif.Mem) : OutsideAvoids (GotSlot (input lower S cleanup) file) f N r args cm:= by
  exact Link.ReturnPinCompilerFor.outsideAvoids_leanLink
    (S := S) (cleanup := cleanup) (file0 := file0)
    (file := file) (h := h) (f := f)
    (N := N) (r := r) (args := args)
    (cm := cm)

theorem attempt_correct {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) {n : String} {f : Clif.Function} (hf : (prog (input lower S cleanup)).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom (SemanticStackBound.Calls (input lower S cleanup) (input lower S cleanup).results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f (SemanticStackBound.stackFn (input lower S cleanup) f) r
      args cs.mem)
    (hr : ClifRun (input lower S cleanup) B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M) (prog (input lower S cleanup)).bare cs) :
    ExecRefines (art (input lower S cleanup) f).fb (art (input lower S cleanup) f).base (xreg 30 r) (step (input lower S cleanup) B file) r
      (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (Clif.runLoop B.env (prog (input lower S cleanup)) (M + 1) cs) := by
  exact Link.ReturnPinCompilerFor.attempt_correct
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (S := S) (cleanup := cleanup)
    (file0 := file0) (file := file) (h := h)
    (B := B) (hB := hB) (hH := hH)
    (n := n) (f := f) (hf := hf)
    (hc := hc) (M := M) (r := r)
    (args := args) (cs := cs) (hX := hX)
    (ho := ho) (hr := hr) (htr := htr)

/-- **The executable compiler is correct for recursive programs** (L1d): `attempt_correct`
without the call-graph premise `¬ CycleFrom`. The outside caller of `f` provides
`frameDrop (art (input lower S cleanup) f).af + (input lower S cleanup).D * M` bytes of stack (`(input lower S cleanup).D`: the largest frame of
the program, `LinkSpec.input`), where `M + 1` bounds the whole-program CLIF run's steps; for that
run (returning, or trapping explicitly) the executable machine run of `file`'s own words refines
it (`ExecRefines`). The stack is proportional to the fuel `M`, not to the run's actual peak call
depth: an overestimate of what the code uses (docs/contracts/e2e.md, "Recursive programs"). -/
theorem attempt_correct_depth {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) {n : String} {f : Clif.Function} (hf : (prog (input lower S cleanup)).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f
      (frameDrop (art (input lower S cleanup) f).af + (input lower S cleanup).D * M) r args cs.mem)
    (hr : ClifRun (input lower S cleanup) B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M) (prog (input lower S cleanup)).bare cs) :
    ExecRefines (art (input lower S cleanup) f).fb (art (input lower S cleanup) f).base (xreg 30 r) (step (input lower S cleanup) B file) r
      (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (Clif.runLoop B.env (prog (input lower S cleanup)) (M + 1) cs) := by
  exact Link.ReturnPinCompilerFor.attempt_correct_depth
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (S := S) (cleanup := cleanup)
    (file0 := file0) (file := file) (h := h)
    (B := B) (hB := hB) (hH := hH)
    (n := n) (f := f) (hf := hf)
    (M := M) (r := r) (args := args)
    (cs := cs) (hX := hX) (ho := ho)
    (hr := hr) (htr := htr)

/-- **The executable compiler is correct for recursive programs, with the stack of the run's peak
call depth** (L1d): `attempt_correct_depth` with `frameDrop (art (input lower S cleanup) f).af + (input lower S cleanup).D * d`
bytes of stack, where `d` bounds the call depth of the whole-program CLIF run (`Clif.DepthLe`:
every state the run from `cs` reaches has at most `d` callers, i.e. at most `d + 1` live
activations), independent of its length (at most `F + 1` steps). For that run (returning, or
trapping explicitly; `TrapsExplicit` under the environment whose program callees run with fuel
`F` and at most `d - 1` callers of their own, `Clif.linkEnvD`) the executable machine run of
`file`'s own words refines it (`ExecRefines`). Each level is charged the largest frame of the
program (`(input lower S cleanup).D`). -/
theorem attempt_correct_peak {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) {n : String} {f : Clif.Function} (hf : (prog (input lower S cleanup)).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f
      (frameDrop (art (input lower S cleanup) f).af + (input lower S cleanup).D * d) r args cs.mem)
    (hr : ClifRun (input lower S cleanup) B f r args cs)
    (hd : Clif.DepthLe B.env (prog (input lower S cleanup)) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d) (prog (input lower S cleanup)).bare cs) :
    ExecRefines (art (input lower S cleanup) f).fb (art (input lower S cleanup) f).base (xreg 30 r) (step (input lower S cleanup) B file) r
      (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (Clif.runLoop B.env (prog (input lower S cleanup)) (F + 1) cs) := by
  exact Link.ReturnPinCompilerFor.attempt_correct_peak
    (admission := E2E.LinkCheck.ReturnPinAdmission.previous) (S := S) (cleanup := cleanup)
    (file0 := file0) (file := file) (h := h)
    (B := B) (hB := hB) (hH := hH)
    (n := n) (f := f) (hf := hf)
    (F := F) (d := d) (r := r)
    (args := args) (cs := cs) (hX := hX)
    (ho := ho) (hr := hr) (hd := hd)
    (htr := htr)

end Link.ReturnPinCompilerWith

namespace Link.ReturnPinCompilerWith
open Backend E2E E2E.LinkCheck
set_option autoImplicit false
set_option Elab.async false
variable {lower : ProductionLowering}

/-- Keep every successful previous attempt with the same complete linked bytes. -/
theorem accepts_previous {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (previous : SemanticCompilerWith.attempt lower S file0 cleanup = .ok file) :
    attempt lower S file0 cleanup = .ok file := by
  have extend : ∀ cleanup,okRSemanticNI (productionStage cleanup) (S.inputProductionWith lower cleanup)
      ((S.inputProductionWith lower cleanup).resultsProductionWith lower cleanup) = true →
      okRReturnPinCalls (productionStage cleanup) (S.inputProductionWith lower cleanup)
        ((S.inputProductionWith lower cleanup).resultsProductionWith lower cleanup) = true := by
    intro cleanup checked
    exact ReturnPinBinary.okB_previous (I := input lower S cleanup) checked
  cases cleanup <;> simp [attempt,ReturnPinAttemptKernel.attemptWith,SemanticCompilerWith.attempt] at previous ⊢
  all_goals
    split at previous
    · cases previous
    · rename_i scope
      rw [if_neg scope]
      split at previous
      · rename_i checked
        rw [if_pos (extend _ checked)]
        exact previous
      · cases previous

end Link.ReturnPinCompilerWith
