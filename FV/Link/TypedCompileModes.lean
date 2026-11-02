import FV.Link.SemanticCompileT

/-! Class-aware typed executable compilation for both production stages. -/

set_option autoImplicit false
namespace Link.TypedCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes Backend
open Link.SemanticCompilerWith
variable {lower : ProductionLowering}

/-- The error of `attempt` when its typed checks fail. -/
def outOkTSMsg : String :=
  "the typed checks on the Stock route's results fail (okRWithTS)"

/-- Keep either the raw or cleanup production stage under the class-aware typed checks. -/
def attempt (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) (cleanup : Bool) :
    Except String ByteArray :=
  let I := S.inputProductionWith lower cleanup
  if okRWithTS (productionStage cleanup) I (I.resultsProductionWith lower cleanup) then
    leanLinkProductionWith lower S file0 cleanup
  else .error outOkTSMsg

theorem attempt_spec {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) :
    SemanticStackBound.okBTS (input lower S cleanup) = true ∧
    leanLinkProductionWith lower S file0 cleanup = .ok file := by
  simp only [attempt] at h
  split at h
  · rename_i checked
    exact ⟨checked, h⟩
  · cases h

/-- **The typed executable compiler on a Stock route is correct**: for `attempt lower S file0 cleanup =
.ok file` and an outside call of a function `f` of the program (no call cycle reachable from it),
the executable machine run of `file`'s own words refines the whole-program CLIF run, each returned
value in the ABI return register of its class (`ExecRefinesT`). -/
theorem attempt_correct {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) {n : String} {f : Clif.Function}
    (hf : (prog (input lower S cleanup)).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S cleanup) (input lower S cleanup).results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f
      (SemanticStackBound.stackFn (input lower S cleanup) f) r args cs.mem)
    (hr : ClifRun (input lower S cleanup) B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M)
      (prog (input lower S cleanup)).bare cs) :
    ExecBytes.ExecRefinesT (art (input lower S cleanup) f).fb (art (input lower S cleanup) f).base
      (xreg 30 r) (step (input lower S cleanup) B file) r
      (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
      (Clif.runLoop B.env (prog (input lower S cleanup)) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := attempt_spec h
  exact binary_correct_exec_provenTS hin
    (SemanticCompilerWith.codeMap_leanLink hl) (ProductionImageWithProof.bin_ok hl) (SemanticCompilerWith.gotOk_leanLink hl) B hB hH hf hc
    M hX ho (SemanticCompilerWith.outsideAvoids_leanLink hl _ _ _ _ _) hr htr

/-- **The typed executable compiler on a Stock route is correct for recursive programs**:
`attempt_correct` without the call-graph premise, the outside caller providing
`frameDrop + D * M` bytes of stack. -/
theorem attempt_correct_depth {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) {n : String} {f : Clif.Function}
    (hf : (prog (input lower S cleanup)).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f
      (frameDrop (art (input lower S cleanup) f).af + (input lower S cleanup).D * M) r args cs.mem)
    (hr : ClifRun (input lower S cleanup) B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M)
      (prog (input lower S cleanup)).bare cs) :
    ExecBytes.ExecRefinesT (art (input lower S cleanup) f).fb (art (input lower S cleanup) f).base
      (xreg 30 r) (step (input lower S cleanup) B file) r
      (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
      (Clif.runLoop B.env (prog (input lower S cleanup)) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := attempt_spec h
  exact binary_correct_exec_depth_provenTS hin
    (SemanticCompilerWith.codeMap_leanLink hl) (ProductionImageWithProof.bin_ok hl) (SemanticCompilerWith.gotOk_leanLink hl) B hB hH hf M hX
    ho (SemanticCompilerWith.outsideAvoids_leanLink hl _ _ _ _ _) hr htr

/-- **The typed executable compiler on a Stock route is correct for recursive programs, with the
stack of the run's peak call depth** (L1d): `attempt_correct_depth` with
`frameDrop + D * d` bytes of stack, `d` bounding the whole-program CLIF run's call depth
(`Clif.DepthLe`). -/
theorem attempt_correct_peak {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) {n : String} {f : Clif.Function}
    (hf : (prog (input lower S cleanup)).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f
      (frameDrop (art (input lower S cleanup) f).af + (input lower S cleanup).D * d) r args cs.mem)
    (hr : ClifRun (input lower S cleanup) B f r args cs)
    (hd : Clif.DepthLe B.env (prog (input lower S cleanup)) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d)
      (prog (input lower S cleanup)).bare cs) :
    ExecBytes.ExecRefinesT (art (input lower S cleanup) f).fb (art (input lower S cleanup) f).base
      (xreg 30 r) (step (input lower S cleanup) B file) r
      (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
      (Clif.runLoop B.env (prog (input lower S cleanup)) (F + 1) cs) := by
  obtain ⟨hin, hl⟩ := attempt_spec h
  exact binary_correct_exec_peak_provenTS hin
    (SemanticCompilerWith.codeMap_leanLink hl) (ProductionImageWithProof.bin_ok hl) (SemanticCompilerWith.gotOk_leanLink hl) B hB hH hf F d
    hX ho (SemanticCompilerWith.outsideAvoids_leanLink hl _ _ _ _ _) hr hd htr

/-- The previous cleanup-only compiler retains its exact definition. -/
theorem attempt_cleanup_eq (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) :
    attempt lower S file0 true = SemanticCompilerWith.attemptT lower S file0 := rfl

end Link.TypedCompilerWith
