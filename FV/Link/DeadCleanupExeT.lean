module

public import FV.Link.DeadCleanupExe
public import FV.E2E.DeadCleanupExecProvenT
public import FV.E2E.LinkScopeIntT

@[expose] public section

/-! # The shipped executable compiler on the typed scope (S11e5 Stage C, slice 8)

`Link.DeadCleanup.compileExe_correctT`: `Link.DeadCleanup.compileExe_correct` (the shipped
pipeline: dead cleanup before `prepare`) for the typed input conditions `InScopePT`, with the
proven typed control families inside the typed link layer (no rule-family premise), for the
output of the Lean linker `Link.DeadCleanup.leanLink` on input that passes the decided output
checks `OutOkTCleanup` (`FV/E2E/LinkOutCleanupT.lean`). The returned values are placed by class
(`ExecRefinesT`).

**Integer specialization**: `compileExe_correct_viaT` re-derives the conclusion of
`Link.DeadCleanup.compileExe_correct` from its exact premises through the typed theorem
(`inScopePT_of_inScopeP`, `outOkTCleanup_of_inScopeP`, `ExecRefinesT.toExecRefines`).
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend LinkSpec

/-- The compiler's pipeline succeeds on every function of `leanLink`'s input (its check). -/
theorem pipe_leanLink {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : S.inputCleanup.resultsCleanupT.all (·.2.toBool) = true := by
  obtain ⟨-, -, -, hr, -⟩ := leanLink_spec h
  exact hr

/-- **`okBCleanupT` of `leanLink`'s input**, from the typed input conditions and the output
checks. -/
theorem okBT_leanLink {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopePT S.inputCleanup = true) (hout : OutOkTCleanup S.inputCleanup = true)
    (h : leanLink S file0 = .ok file) : okBCleanupT S.inputCleanup = true := by
  have := okT_of_inScopeCleanupT hin hout (pipe_leanLink h) (leanLink_linkerOk h)
  rw [input_withDepth S] at this
  rw [okBCleanupT, S.inputCleanup_results]
  exact this

/-- **The shipped executable compiler is correct on the typed scope**
(`Link.DeadCleanup.compileExe_correct` for `InScopePT`): for `leanLink S file0 = .ok file` on a
typed in-scope input passing the output checks, and an outside call of a function `f` of the
program (no call cycle reachable from it), the executable machine run of `file`'s own words
refines the whole-program CLIF run, each returned value in the ABI return register of its class
(`ExecRefinesT`). -/
theorem compileExe_correctT {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopePT S.inputCleanup = true) (hout : OutOkTCleanup S.inputCleanup = true)
    (h : leanLink S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
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
      (Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs) :=
  binary_correct_exec_provenT (okBT_leanLink hin hout h)
    (codeMap_leanLink h) (binOk_leanLink h) (gotOk_leanLink h) B hB hH hf hc M hX ho
    (outsideAvoids_leanLink h _ _ _ _ _) hr htr

/-! ## Integer specialization -/

/-- A returning whole-program run of a subset-E function returns integers. -/
theorem returns_int_of_inScopeP {S : LinkSpec} (hin : InScopeP S.inputCleanup = true) (B : BaseEnv)
    {n : String} {f : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hr : ClifRun S.inputCleanup B f r args cs) (N : Nat) :
    ∀ vals cm, Clif.runLoop B.env (prog S.inputCleanup) N cs = .returned vals cm →
      ∀ v ∈ vals, v.ty.isInt = true := by
  intro vals cm hrun v hv
  have hP : prog S.inputCleanup = S.inputCleanup.prog := by
    show progOf S.inputCleanup.resultsCleanup = _
    rw [S.inputCleanup_results, progOf_resultsCleanupT]
  have hfs : ∀ g ∈ S.inputCleanup.prog.funcs, fnScopeB g = true := by
    simp only [InScopeP, Bool.and_eq_true, List.all_eq_true] at hin
    exact hin.2
  have hfm := (Clif.Program.func?_some hf).1
  rw [hP] at hrun hfm
  have hrt := Clif.runLoop_returned_tys
    (fun g hg => linkFreeB_sound (fnScope_parts (hfs g hg)).2.2.2.2.2.2.1) N cs vals cm
    (runInv_entry hfm hr.entry) hrun
  have hbot : cs.bottom = f := by simp [Clif.State.bottom, hr.entry.callers, hr.entry.func]
  rw [hbot] at hrt
  have hm : v.ty ∈ Clif.AbiParam.tys f.sig.returns := hrt ▸ List.mem_map_of_mem hv
  obtain ⟨q, hq, hqt⟩ := List.mem_map.mp hm
  rw [← hqt]
  exact returns_isInt_of_functionE (fnScope_parts (hfs f hfm)).1 q hq

/-- The typed premises of an integer `compileExe` success. -/
theorem typedPremises_of_compileExe {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) :
    InScopePT S.inputCleanup = true ∧ OutOkTCleanup S.inputCleanup = true ∧
      leanLink S file0 = .ok file := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact ⟨inScopePT_of_inScopeP hin, outOkTCleanup_of_inScopeP hin (leanLink_linkerOk hl), hl⟩

/-- **`Link.DeadCleanup.compileExe_correct` through the typed theorem**: its conclusion from its
exact premises, by `compileExe_correctT` (integer specialization). -/
theorem compileExe_correct_viaT {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs) :
    ExecRefines (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs) := by
  obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe h
  exact (compileExe_correctT hin hout hl B hB hH hf hc M hX ho hr htr).toExecRefines
    fun vals cm hrun => returns_int_of_inScopeP (compileExe_spec h).1 B hf hr (M + 1) vals cm hrun

end Link.DeadCleanup
