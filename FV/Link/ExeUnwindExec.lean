import FV.Link.ExeUnwind
import FV.E2E.DeadCleanupExecUnwind

/-!
# The executable compiler on the exceptional edges, on the executable's bytes (S10g, #404)

`compileExe_correct_unwind{,_peak}` (`FV/Link/ExeUnwind.lean`) are about the linked machine with
unwinding (`LinkSysU.machU`: nested activations, each frame unwound with its function's tables)
plus the fact that libunwind's lookup in the written executable returns those tables. Here the
conclusion is about **the executable machine with unwinding** `E2E.DeadCleanupExecBytes.stepU`
(`FV/E2E/DeadCleanupExecUnwind.lean`): the processor on the file's words, calls of code outside
the program and TLS by the base hooks, and a raising base callee followed by phase 2 of the
unwinder on the **file's** tables, frame by frame (`Walk`), until a landing pad, an error, or the
exception leaving the program.

* `compileExe_correct_unwind_exec_of_good` (entries without a reachable call cycle) and
  `compileExe_correct_unwind_exec_peak_of_good` (the run's peak call depth `d`): for
  `compileExeU S file0 = .ok file`, an outside call of `f` in `r` (`compileExe_correct{,_peak}`'s
  premises: the image intact, the boundary contract `OutsideCall`, the reference CLIF entry
  `ClifRun`, the hooks' `HooksSim`), the linked program with unwinding `L` of the input with that
  call's world (`compileExe_correct_unwind{,_peak}`'s premises `BaseU`, `OkUNI` and the run premises
  `TrapsExplicitX`, `DepthLeX`), the raising base callees reading no relocated instruction byte
  (`UnwSim`) and the outside caller's call instruction no code of the program (`hra1`, the byte
  before the return address, where libunwind looks up the caller's frame): the executable machine
  with unwinding run from `r` refines the whole-program run with unwinding (`ExecRefinesU`: a
  return, a trap, the exception leaving `f` with the exception object in x0, the live CLIF bytes
  outside the relocated instruction bytes as the CLIF memory). **Open**: the per-state facts of
  the model's run with unwinding (`RunOkU`, the counterpart of `binary_correct_exec_of_good`'s
  `RunOk`).
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  Backend.Proof LinkSpec

/-- The file's unwind tables are the compiled functions' (`compileExeU_tables`). -/
theorem tabsOk_of {S : LinkSpec} {file0 file : ByteArray} (h : compileExeU S file0 = .ok file) :
    TabsOk S.inputCleanup file :=
  fun _ hg _ h1 h2 => compileExeU_tables h hg h1 h2

/-- **The transfer of the linked machine's refinement with unwinding to the executable**: the
facts of `compileExeU`'s output the transfer needs. -/
theorem exec_of_armU {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    {f : Clif.Function} (hf : f ∈ (prog S.inputCleanup).funcs) {K : Nat}
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (frameDrop (art S.inputCleanup f).af + K) r args cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs) (U : LinkSysU) (hUS : UnwSim S.inputCleanup U.Ub)
    (hra1 : ¬ img S.inputCleanup (xreg 30 r - 1)) {M : Nat}
    (hrun : RunOkU S.inputCleanup B file U M f (modelOf S.inputCleanup f r)) {o : Clif.XOutcome}
    (hA : ArmRefinesU (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      ((uSys S.inputCleanup B U).machU M f) (modelOf S.inputCleanup f r) o) :
    ExecRefinesU (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (stepU S.inputCleanup B U.Ub file) r (DeadCleanupBinCheck.RelocAt S.inputCleanup) o := by
  obtain ⟨hc, -⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec hc
  have hI := okB_leanLink hin hl
  have hbin := binOk_leanLink hl
  have hfacts := binFacts_of_checks hI hbin
  have hL0 := okBCleanup_sound hI (baseOk_F (F' := worldF S.inputCleanup f K r) hB)
    fun _ h => .inr h
  have hro : ∀ a b, BinCheck.roByte S.inputCleanup S.data a = some b → r.mem a = b :=
    fun a b h => hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, -⟩ := premises hL0 hf hro ho hr
  have hL' := okBCleanup_sound hI (baseOk_F (F' := img S.inputCleanup) hB) fun _ h => h
  exact exec_of_modelU hI (fun g hg => fnOk hI hbin hL' hg) (tabsOk_of h) hUS hf
    (by rw [← r_modelOf S.inputCleanup f r]; exact hent.pc) hent.raOutside hra1
    (hfacts.modelOf_ne hX) hrun hA

/-- **The executable compiler is correct on the exceptional edges, on the executable's bytes,
for the run's peak call depth** (given the per-state facts `RunOkU` of the model's run): for
`compileExeU S file0 = .ok file`, an outside call of `f` in `r` with
`frameDrop + (D * d + pbMax)` bytes of stack (`compileExe_correct_peak`'s premises) and the linked program
with unwinding `L` of the input with this call's world (`compileExe_correct_unwind_peak`'s
premises), the executable machine with unwinding (`stepU`: the file's words, the hooks, and phase
2 of the unwinder on the file's tables) run from `r` refines the whole-program run with
unwinding of at most `Fu + 1` steps (`ExecRefinesU`). -/
theorem compileExe_correct_unwind_exec_peak_of_good {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    {n : String} {f : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (Fu d : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args
      cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (L : LinkSysU) (hLs : L.toLinkSys =
      LinkSys.ofInputCleanup S.inputCleanup B
        (worldF S.inputCleanup f (S.inputCleanup.D * d + pbMax S.inputCleanup) r))
    (hb : BaseU L) (hNI : L.OkUNI) (hUS : UnwSim S.inputCleanup L.Ub)
    (hra1 : ¬ img S.inputCleanup (xreg 30 r - 1))
    (hd : Clif.DepthLeX L.envX L.P d cs.toX)
    (htr : TrapsExplicitX ((L.peakX Fu).envRX d f) L.P.bare cs)
    (hrun : RunOkU S.inputCleanup B file L d f (modelOf S.inputCleanup f r)) :
    ExecRefinesU (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (stepU S.inputCleanup B L.Ub file) r (DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoopX L.envX L.P (Fu + 1) cs.toX) := by
  have hfm := (Clif.Program.func?_some hf).1
  obtain ⟨hc, -⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec hc
  have hI := okB_leanLink hin hl
  have hbin := binOk_leanLink hl
  have hfacts := binFacts_of_checks hI hbin
  have hB' := baseOk_F (F' := worldF S.inputCleanup f (S.inputCleanup.D * d + pbMax S.inputCleanup) r) hB
  have hF0 : ∀ a, (LinkSys.ofInputCleanup S.inputCleanup B
      (worldF S.inputCleanup f (S.inputCleanup.D * d + pbMax S.inputCleanup) r)).Img a →
      worldF S.inputCleanup f (S.inputCleanup.D * d + pbMax S.inputCleanup) r a := fun _ h => .inr h
  have hL0 := okBCleanup_sound hI hB' hF0
  have hro : ∀ a b, BinCheck.roByte S.inputCleanup S.data a = some b → r.mem a = b :=
    fun a b h => hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ := premises hL0 hfm hro ho hr
  have hmach := machU_uSys hLs d f
  obtain ⟨L0, Ub, envX, XRb, crunX⟩ := L
  change L0 = _ at hLs
  subst hLs
  have hA := (compileExe_correct_unwind_peak h B _ hB' hF0 _ rfl hb hNI (LinkSys.budget_K _ hL0)
    hfm Fu d hent ⟨hres, (LinkSys.budget_K _ hL0).2 d f hfm⟩ rfl hgfree himg hbe hargs hr.entry
    hsav hrel hpl hd htr).2
  rw [hmach] at hA
  exact exec_of_armU h B hB hfm hX ho hr _ hUS hra1 hrun hA

/-- **The executable compiler is correct on the exceptional edges, on the executable's bytes**
(entries without a reachable call cycle, stack bound `stackFn`; given the per-state facts
`RunOkU` of the model's run): `compileExe_correct_unwind_exec_peak_of_good` for
`compileExe_correct`'s and `compileExe_correct_unwind`'s premises. -/
theorem compileExe_correct_unwind_exec_of_good {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    {n : String} {f : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs.mem)
    (hr : ClifRun S.inputCleanup B f r args cs)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.inputCleanup B
      (worldF S.inputCleanup f (DeadCleanupStackBound.bud S.inputCleanup f) r))
    (hb : BaseU L) (hNI : L.OkUNI) (hUS : UnwSim S.inputCleanup L.Ub)
    (hra1 : ¬ img S.inputCleanup (xreg 30 r - 1))
    (htr : TrapsExplicitX (L.stdX.envRX M f) L.P.bare cs)
    (hrun : RunOkU S.inputCleanup B file L M f (modelOf S.inputCleanup f r)) :
    ExecRefinesU (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (stepU S.inputCleanup B L.Ub file) r (DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoopX L.envX L.P (M + 1) cs.toX) := by
  have hfm := (Clif.Program.func?_some hf).1
  obtain ⟨hcU, -⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec hcU
  have hI := okB_leanLink hin hl
  have hbin := binOk_leanLink hl
  have hfacts := binFacts_of_checks hI hbin
  have hn := (DeadCleanupStackBound.goodN_iff hI).2 ⟨f, hf, hc⟩
  have hf' : (progOf S.inputCleanup.resultsCleanup).func? n = some f := hf
  unfold DeadCleanupStackBound.goodN at hn
  rw [hf'] at hn
  obtain ⟨b, hbb⟩ := Option.isSome_iff_exists.1 hn
  have hbud : DeadCleanupStackBound.bud S.inputCleanup f = b := by
    simp [DeadCleanupStackBound.bud, hbb]
  have hB' := baseOk_F (F' := worldF S.inputCleanup f (DeadCleanupStackBound.bud S.inputCleanup f) r) hB
  have hF0 : ∀ a, (LinkSys.ofInputCleanup S.inputCleanup B
      (worldF S.inputCleanup f (DeadCleanupStackBound.bud S.inputCleanup f) r)).Img a →
      worldF S.inputCleanup f (DeadCleanupStackBound.bud S.inputCleanup f) r a := fun _ h => .inr h
  have hL0 := okBCleanup_sound hI hB' hF0
  have hro : ∀ a b, BinCheck.roByte S.inputCleanup S.data a = some b → r.mem a = b :=
    fun a b h => hX a b (hfacts.data a b h).1 (hfacts.data a b h).2
  obtain ⟨hent, hres, hgfree, himg, hbe, hargs, hsav, hrel, hpl⟩ := premises hL0 hfm hro ho hr
  have hκ := DeadCleanupStackBound.budget_of hI B
    (worldF S.inputCleanup f (DeadCleanupStackBound.bud S.inputCleanup f) r)
  have hκf : ∀ M, (LinkSys.ofInputCleanup S.inputCleanup B
      (worldF S.inputCleanup f (DeadCleanupStackBound.bud S.inputCleanup f) r)).hybrid
      (DeadCleanupStackBound.budO S.inputCleanup) (DeadCleanupStackBound.budMax S.inputCleanup)
      M f = DeadCleanupStackBound.bud S.inputCleanup f := fun M => by
    simp [LinkSys.hybrid, hbb, hbud]
  have hmach := machU_uSys hLs M f
  obtain ⟨L0, Ub, envX, XRb, crunX⟩ := L
  change L0 = _ at hLs
  subst hLs
  have hA := (compileExe_correct_unwind h B _ hB' hF0 _ rfl hb hNI hκ hfm M hent
    (by rw [hκf]; exact ⟨hres, by rw [← hκf M]; exact hκ.2 M f hfm⟩) (by rw [hκf]; rfl)
    (by rw [hκf]; exact hgfree) himg hbe hargs
    hr.entry hsav hrel hpl htr).2
  rw [hmach] at hA
  exact exec_of_armU h B hB hfm hX ho hr _ hUS hra1 hrun hA

end Link.DeadCleanup
