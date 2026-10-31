import FV.Link.Exe
import FV.E2E.ExecProvenT
import FV.E2E.LinkScopeIntT

/-! # The executable compiler on the typed scope (S11e5 Stage C, slice 8)

`Link.compileExe_correctT` (and `_depthT`, `_peakT`): `Link.compileExe_correct*` for the typed
input conditions `InScopePT` (`FV/E2E/LinkScopeDefsT.lean`: float values in movement forms,
float parameters and returns), with the proven typed control families (`E2E.typedRules_program`)
inside the typed link layer (no rule-family premise), for the output of the Lean linker `leanLink`
on input that passes the decided output checks `OutOkT` (`FV/E2E/LinkOutT.lean`: the facts about
the compiler's own output proven only for subset E today). Same conclusion as the integer
theorems, except that the returned values are placed by class (`ExecRefinesT`: integers in
x0, x1, …, floats in v0, v1, …).

**Integer specializations**: `compileExe_correct_viaT` (and `_depth`, `_peak`) re-derive the
conclusions of `Link.compileExe_correct*` from their exact premises through the typed theorems:
`InScopeP` gives `InScopePT` (`inScopePT_of_inScopeP`) and `OutOkT` (`outOkT_of_inScopeP`, from
the integer chain's own-output facts), and a subset-E function returns integers, for which
`ExecRefinesT` is `ExecRefines` (`ExecRefinesT.toExecRefines`).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes Backend LinkSpec

/-- The compiler's pipeline succeeds on every function of `leanLink`'s input (its check). -/
theorem pipe_leanLink {S : LinkSpec} {file0 file : ByteArray}
    (h : leanLink S file0 = .ok file) : S.input.resultsT.all (·.2.toBool) = true := by
  obtain ⟨-, -, -, hr, -⟩ := leanLink_spec h
  exact hr

/-- **`okBT` of `leanLink`'s input**, from the typed input conditions and the output checks. -/
theorem okBT_leanLink {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopePT S.input = true) (hout : OutOkT S.input = true)
    (h : leanLink S file0 = .ok file) : okBT S.input = true := by
  have := okT_of_inScopeT hin hout (pipe_leanLink h) (leanLink_linkerOk h)
  rw [S.input_withDepth] at this
  rw [okB_fallbackT rfl]
  exact this

/-- **The executable compiler is correct on the typed scope** (`compileExe_correct` for
`InScopePT`): for `leanLink S file0 = .ok file` on a typed in-scope input passing the output
checks, and an outside call of a function `f` of the program (no call cycle reachable from it),
the executable machine run of `file`'s own words refines the whole-program CLIF run, each returned
value in the ABI return register of its class (`ExecRefinesT`). -/
theorem compileExe_correctT {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopePT S.input = true) (hout : OutOkT S.input = true)
    (h : leanLink S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f (StackBound.stackFn S.input f) r
      args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs) :
    ExecRefinesT (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs) :=
  binary_correct_exec_provenT (okBT_leanLink hin hout h)
    (codeMap_leanLink h) (binOk_leanLink h) (gotOk_leanLink h) B hB hH hf hc M hX ho
    (outsideAvoids_leanLink h _ _ _ _ _) hr htr

/-- **`compileExe_correctT` for recursive programs** (`compileExe_correct_depth` for
`InScopePT`). -/
theorem compileExe_correct_depthT {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopePT S.input = true) (hout : OutOkT S.input = true)
    (h : leanLink S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f
      (frameDrop (art S.input f).af + (S.input.D * M + pbMax S.input)) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs) :
    ExecRefinesT (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs) :=
  binary_correct_exec_depth_provenT (okBT_leanLink hin hout h)
    (codeMap_leanLink h) (binOk_leanLink h) (gotOk_leanLink h) B hB hH hf M hX ho
    (outsideAvoids_leanLink h _ _ _ _ _) hr htr

/-- **`compileExe_correctT` with the stack of the run's peak call depth**
(`compileExe_correct_peak` for `InScopePT`). -/
theorem compileExe_correct_peakT {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopePT S.input = true) (hout : OutOkT S.input = true)
    (h : leanLink S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f
      (frameDrop (art S.input f).af + (S.input.D * d + pbMax S.input)) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.input) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs) :
    ExecRefinesT (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (F + 1) cs) :=
  binary_correct_exec_peak_provenT (okBT_leanLink hin hout h)
    (codeMap_leanLink h) (binOk_leanLink h) (gotOk_leanLink h) B hB hH hf F d hX ho
    (outsideAvoids_leanLink h _ _ _ _ _) hr hd htr

/-! ## Integer specializations -/

/-- The typed premises of an integer `compileExe` success. -/
theorem typedPremises_of_compileExe {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) :
    InScopePT S.input = true ∧ OutOkT S.input = true ∧ leanLink S file0 = .ok file := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact ⟨inScopePT_of_inScopeP hin, outOkT_of_inScopeP hin (leanLink_linkerOk hl), hl⟩

/-- A returning whole-program run of a subset-E function returns integers (its signature's). -/
theorem returns_int_of_inScopeP {S : LinkSpec} (hin : InScopeP S.input = true) (B : BaseEnv)
    {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hr : ClifRun S.input B f r args cs) (N : Nat) :
    ∀ vals cm, Clif.runLoop B.env (prog S.input) N cs = .returned vals cm →
      ∀ v ∈ vals, v.ty.isInt = true := by
  intro vals cm hrun v hv
  have hP : prog S.input = S.input.prog := by
    show progOf S.input.results = _
    rw [LinkInput.results_fallback rfl, progOf_resultsT]
  have hfs : ∀ g ∈ S.input.prog.funcs, fnScopeB g = true := by
    simp only [InScopeP, Bool.and_eq_true, List.all_eq_true] at hin
    exact hin.2
  have hfm := (Clif.Program.func?_some hf).1
  rw [hP] at hrun hfm
  have hrt := Clif.runLoop_returned_tys
    (fun g hg => linkFreeB_sound (fnScope_parts (hfs g hg)).2.2.2.2.2.2.1) N cs vals cm
    (runInv_entry hfm hr.entry) hrun
  have hbot : cs.bottom = f := by simp [Clif.State.bottom, hr.entry.callers, hr.entry.func]
  rw [hbot] at hrt
  have hE := (fnScope_parts (hfs f hfm)).1
  have hm : v.ty ∈ Clif.AbiParam.tys f.sig.returns := hrt ▸ List.mem_map_of_mem hv
  obtain ⟨q, hq, hqt⟩ := List.mem_map.mp hm
  simp only [Compile.functionE, Compile.sigE, Bool.and_eq_true, List.all_eq_true] at hE
  have := hE.1.1.1.2 q hq
  simp only [Compile.tyE, Bool.and_eq_true] at this
  rw [← hqt]
  exact this.1

/-- The whole-program runs of an integer `compileExe` success return integers. -/
theorem returns_int_of_compileExe {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) {n : String} {f : Clif.Function}
    (hf : (prog S.input).func? n = some f) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hr : ClifRun S.input B f r args cs) (N : Nat) :
    ∀ vals cm, Clif.runLoop B.env (prog S.input) N cs = .returned vals cm →
      ∀ v ∈ vals, v.ty.isInt = true :=
  returns_int_of_inScopeP (compileExe_spec h).1 B hf hr N

/-- **`compileExe_correct` through the typed theorem**: its conclusion from its exact premises,
by `compileExe_correctT` (integer specialization). -/
theorem compileExe_correct_viaT {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f (StackBound.stackFn S.input f) r
      args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs) := by
  obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe h
  exact (compileExe_correctT hin hout hl B hB hH hf hc M hX ho hr htr).toExecRefines
    fun vals cm hrun => returns_int_of_compileExe h B hf hr (M + 1) vals cm hrun

/-- **`compileExe_correct_depth` through the typed theorem.** -/
theorem compileExe_correct_depth_viaT {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f
      (frameDrop (art S.input f).af + (S.input.D * M + pbMax S.input)) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (htr : TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (M + 1) cs) := by
  obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe h
  exact (compileExe_correct_depthT hin hout hl B hB hH hf M hX ho hr htr).toExecRefines
    fun vals cm hrun => returns_int_of_compileExe h B hf hr (M + 1) vals cm hrun

/-- **`compileExe_correct_peak` through the typed theorem.** -/
theorem compileExe_correct_peak_viaT {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.input B))
    (hH : HooksSim S.input B) {n : String} {f : Clif.Function} (hf : (prog S.input).func? n = some f)
    (F d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f
      (frameDrop (art S.input f).af + (S.input.D * d + pbMax S.input)) r args cs.mem)
    (hr : ClifRun S.input B f r args cs)
    (hd : Clif.DepthLe B.env (prog S.input) d cs)
    (htr : TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs) :
    ExecRefines (art S.input f).fb (art S.input f).base (xreg 30 r) (step S.input B file) r
      (RelocAt S.input) (Clif.runLoop B.env (prog S.input) (F + 1) cs) := by
  obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe h
  exact (compileExe_correct_peakT hin hout hl B hB hH hf F d hX ho hr hd htr).toExecRefines
    fun vals cm hrun => returns_int_of_compileExe h B hf hr (F + 1) vals cm hrun

end Link
