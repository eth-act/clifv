import FV.Link.SemanticExeWith
import FV.E2E.SemanticExecTS

/-! # The typed executable compiler on a Stock route (#722)

`Link.SemanticCompilerWith.attemptT lower S file0`: the Stock route's pipeline and link
(`leanLinkProductionWith lower S file0 true`: per function the Stock lowering `lower`, falling
back to `lowerFunction` where it fails, then the dead cleanup; Cranelift's code where the Stock
lowerings are proven), accepted when the typed checks `okRWithTS` hold on its results: per
function the Stock validator `SemanticNI.check` on an integer function without `sret` parameter,
or the typed validators (`lowerCheckT`/`lowerCheckTCF`) on `lowerFunction`'s output, which admit
the proven float operations. So float functions are verified inside the same region as the
Stock-lowered integer functions, with the code the Stock route emits (no generated-code change).

Correctness: `attemptT_correct` (no call cycle reachable), `attemptT_correct_depth` (any
program, the stack of the depth-`M` budget), `attemptT_correct_peak` (the stack of the run's
peak call depth), each returned value in the ABI return register of its class
(`ExecBytes.ExecRefinesT`; integer returns in x0.., `ExecRefinesT.toExecRefines`). -/

set_option autoImplicit false
namespace Link.SemanticCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes Backend
variable {lower : ProductionLowering}

/-- The error of `attemptT` when its typed checks fail. -/
def outOkTSMsg : String :=
  "the typed checks on the Stock route's results fail (okRWithTS)"

/-- **The typed executable compiler on the Stock route `lower`** (#722): the dead-cleanup Stock
pipeline's results, accepted when the typed checks `okRWithTS` hold, linked by
`leanLinkProductionWith`. -/
def attemptT (lower : ProductionLowering) (S : LinkSpec) (file0 : ByteArray) :
    Except String ByteArray :=
  let I := S.inputProductionWith lower true
  if okRWithTS (productionStage true) I (I.resultsProductionWith lower true) then
    leanLinkProductionWith lower S file0 true
  else .error outOkTSMsg

theorem attemptT_spec {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) :
    SemanticStackBound.okBTS (input lower S true) = true ∧
    leanLinkProductionWith lower S file0 true = .ok file := by
  simp only [attemptT] at h
  split at h
  · rename_i checked
    exact ⟨checked, h⟩
  · cases h

/-- **The typed executable compiler on a Stock route is correct**: for `attemptT lower S file0 =
.ok file` and an outside call of a function `f` of the program (no call cycle reachable from it),
the executable machine run of `file`'s own words refines the whole-program CLIF run, each returned
value in the ABI return register of its class (`ExecRefinesT`). -/
theorem attemptT_correct {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys (input lower S true) B))
    (hH : HooksSim (input lower S true) B) {n : String} {f : Clif.Function}
    (hf : (prog (input lower S true)).func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S true) (input lower S true).results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) f
      (SemanticStackBound.stackFn (input lower S true) f) r args cs.mem)
    (hr : ClifRun (input lower S true) B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog (input lower S true)) B.env M)
      (prog (input lower S true)).bare cs) :
    ExecBytes.ExecRefinesT (art (input lower S true) f).fb (art (input lower S true) f).base
      (xreg 30 r) (step (input lower S true) B file) r
      (RelocAtWithResults (input lower S true) (input lower S true).results)
      (Clif.runLoop B.env (prog (input lower S true)) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := attemptT_spec h
  exact binary_correct_exec_provenTS hin
    (codeMap_leanLink hl) (ProductionImageWithProof.bin_ok hl) (gotOk_leanLink hl) B hB hH hf hc
    M hX ho (outsideAvoids_leanLink hl _ _ _ _ _) hr htr

/-- **The typed executable compiler on a Stock route is correct for recursive programs**:
`attemptT_correct` without the call-graph premise, the outside caller providing
`frameDrop + (D * M + pbMax)` bytes of stack (statement change for #581: the unrolled stack
probes of the deepest frame touch up to `pbMax` bytes below the frames). -/
theorem attemptT_correct_depth {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys (input lower S true) B))
    (hH : HooksSim (input lower S true) B) {n : String} {f : Clif.Function}
    (hf : (prog (input lower S true)).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) f
      (frameDrop (art (input lower S true) f).af +
        ((input lower S true).D * M + pbMax (input lower S true))) r args cs.mem)
    (hr : ClifRun (input lower S true) B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog (input lower S true)) B.env M)
      (prog (input lower S true)).bare cs) :
    ExecBytes.ExecRefinesT (art (input lower S true) f).fb (art (input lower S true) f).base
      (xreg 30 r) (step (input lower S true) B file) r
      (RelocAtWithResults (input lower S true) (input lower S true).results)
      (Clif.runLoop B.env (prog (input lower S true)) (M + 1) cs) := by
  obtain ⟨hin, hl⟩ := attemptT_spec h
  exact binary_correct_exec_depth_provenTS hin
    (codeMap_leanLink hl) (ProductionImageWithProof.bin_ok hl) (gotOk_leanLink hl) B hB hH hf M hX
    ho (outsideAvoids_leanLink hl _ _ _ _ _) hr htr

/-- **The typed executable compiler on a Stock route is correct for recursive programs, with the
stack of the run's peak call depth** (L1d): `attemptT_correct_depth` with
`frameDrop + (D * d + pbMax)` bytes of stack, `d` bounding the whole-program CLIF run's call depth
(`Clif.DepthLe`). -/
theorem attemptT_correct_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys (input lower S true) B))
    (hH : HooksSim (input lower S true) B) {n : String} {f : Clif.Function}
    (hf : (prog (input lower S true)).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) f
      (frameDrop (art (input lower S true) f).af +
        ((input lower S true).D * d + pbMax (input lower S true))) r args cs.mem)
    (hr : ClifRun (input lower S true) B f r args cs)
    (hd : Clif.DepthLe B.env (prog (input lower S true)) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog (input lower S true)) B.env F d)
      (prog (input lower S true)).bare cs) :
    ExecBytes.ExecRefinesT (art (input lower S true) f).fb (art (input lower S true) f).base
      (xreg 30 r) (step (input lower S true) B file) r
      (RelocAtWithResults (input lower S true) (input lower S true).results)
      (Clif.runLoop B.env (prog (input lower S true)) (F + 1) cs) := by
  obtain ⟨hin, hl⟩ := attemptT_spec h
  exact binary_correct_exec_peak_provenTS hin
    (codeMap_leanLink hl) (ProductionImageWithProof.bin_ok hl) (gotOk_leanLink hl) B hB hH hf F d
    hX ho (outsideAvoids_leanLink hl _ _ _ _ _) hr hd htr

end Link.SemanticCompilerWith
