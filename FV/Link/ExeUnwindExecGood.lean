import FV.Link.OptExeUnwindExec
import FV.E2E.DeadCleanupExecUnwindGood
import FV.E2E.LinkArmUProgGood

/-!
# The executable compilers on the exceptional edges, on the executable's bytes, proven (S10g, #404)

`compileExe_correct_unwind_exec{,_peak}_of_good` and
`compileExeOpt_correct_unwind_exec_peak_of_good` (`FV/Link/ExeUnwindExec.lean`,
`FV/Link/OptExeUnwindExec.lean`) without their premise `RunOkU` (the per-state facts of the
model's run with unwinding): `RunOkU` is proven (`runOkU_of_good`,
`FV/E2E/DeadCleanupExecUnwindGood.lean`) from the per-state facts the linking statement with
unwinding exports for a returning, trapping or unwinding run (`backend_correct_program_budgetUG'`,
`_peakUG'`), the code map check (`codeMap_leanLink`), `leanLink`'s output having no GOT slot
(`leanLink_gotSlot`), and the base hooks' contract `HooksSim` — the premise
`compileExe_correct`'s executable-bytes theorem has too. For a run that gets stuck or runs out of
fuel `ExecRefinesU` holds trivially.

* **`compileExe_correct_unwind_exec_peak`** (the run's peak call depth `d`),
  **`compileExe_correct_unwind_exec`** (entries without a reachable call cycle),
  **`compileExeOpt_correct_unwind_exec_peak`** (through the mid-end).
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes Backend
  Backend.Proof LinkSpec

/-- The run outcomes `ExecRefinesU` says something about: a return, a trap or an exception. -/
theorem execRefinesU_of_ended {fb : FnBin} {base ra : BitVec 64}
    {step : Arm.ArmState → Arm.ArmState} {s : Arm.ArmState} {R : BitVec 64 → Prop}
    {o : Clif.XOutcome}
    (h : ((∃ vals cm, o = .returned vals cm) ∨ (∃ c, o = .trapped c) ∨
      (∃ e cm, o = .unwound e cm)) → ExecRefinesU fb base ra step s R o) :
    ExecRefinesU fb base ra step s R o := by
  cases o with
  | returned vals cm => exact h (.inl ⟨_, _, rfl⟩)
  | trapped c => exact h (.inr (.inl ⟨_, rfl⟩))
  | unwound e cm => exact h (.inr (.inr ⟨_, _, rfl⟩))
  | stuck _ => trivial
  | outOfFuel => trivial

/-- **The executable compiler is correct on the exceptional edges, on the executable's bytes,
for the run's peak call depth**: for `compileExeU S file0 = .ok file`, an outside call of `f` in
`r` with `frameDrop + (D * d + pbMax)` bytes of stack (`compileExe_correct_peak`'s premises, the hooks'
contract `HooksSim`) and the linked program with unwinding `L` of the input with this call's world
(`compileExe_correct_unwind_peak`'s premises), the raising base callees reading no relocated
instruction byte (`UnwSim`) and the outside caller's call instruction no code of the program
(`hra1`), the executable machine with unwinding (`stepU`: the file's words, the hooks, and phase 2
of the unwinder on the file's tables) run from `r` refines the whole-program run with unwinding
of at most `Fu + 1` steps (`ExecRefinesU`). -/
theorem compileExe_correct_unwind_exec_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B)
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
    (htr : TrapsExplicitX ((L.peakX Fu).envRX d f) L.P.bare cs) :
    ExecRefinesU (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (stepU S.inputCleanup B L.Ub file) r (DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoopX L.envX L.P (Fu + 1) cs.toX) := by
  refine execRefinesU_of_ended fun hout => ?_
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
  have hL' := okBCleanup_sound hI (baseOk_F (F' := img S.inputCleanup) hB) fun _ h => h
  have hF : ∀ g ∈ (prog S.inputCleanup).funcs, FnOk S.inputCleanup file g :=
    fun g hg => fnOk hI hbin hL' hg
  have hra : ∀ k < (art S.inputCleanup f).fb.words.size,
      xreg 30 (modelOf S.inputCleanup f r) ≠
        (art S.inputCleanup f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hent.raOutside
  obtain ⟨hLok, hU, -⟩ := compileExeU_facts h hB' hF0 hLs hb
  have hgood : L.RunGoodLU d f (modelOf S.inputCleanup f r) := by
    obtain ⟨L0, Ub, envX, XRb, crunX⟩ := L
    change L0 = _ at hLs
    subst hLs
    exact backend_correct_program_peakUG' _ hLok hU hNI (LinkSys.budget_K _ hL0) hfm Fu d hent
      ⟨hres, (LinkSys.budget_K _ hL0).2 d f hfm⟩ rfl hgfree himg hbe hargs hr.entry hsav hrel hpl hd
      htr hout
  exact compileExe_correct_unwind_exec_peak_of_good h B hB hf Fu d hX ho hr L hLs hb hNI hUS hra1
    hd htr (runOkU_of_good hI (codeMap_leanLink hl) hF hH (leanLink_gotSlot hl)
      (fun g hg => destsInt_of_ok hL' hg) hfm hra (runGoodLU_uSys hLs hgood))

/-- **The executable compiler is correct on the exceptional edges, on the executable's bytes**
(entries without a reachable call cycle, stack bound `stackFn`): `compileExe_correct`'s and
`compileExe_correct_unwind`'s premises, the raising base callees reading no relocated instruction
byte (`UnwSim`) and the outside caller's call instruction no code of the program (`hra1`). -/
theorem compileExe_correct_unwind_exec {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B))
    (hH : HooksSim S.inputCleanup B)
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
    (htr : TrapsExplicitX (L.stdX.envRX M f) L.P.bare cs) :
    ExecRefinesU (art S.inputCleanup f).fb (art S.inputCleanup f).base (xreg 30 r)
      (stepU S.inputCleanup B L.Ub file) r (DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoopX L.envX L.P (M + 1) cs.toX) := by
  refine execRefinesU_of_ended fun hout => ?_
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
  have hB' := baseOk_F
    (F' := worldF S.inputCleanup f (DeadCleanupStackBound.bud S.inputCleanup f) r) hB
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
  have hL' := okBCleanup_sound hI (baseOk_F (F' := img S.inputCleanup) hB) fun _ h => h
  have hF : ∀ g ∈ (prog S.inputCleanup).funcs, FnOk S.inputCleanup file g :=
    fun g hg => fnOk hI hbin hL' hg
  have hra : ∀ k < (art S.inputCleanup f).fb.words.size,
      xreg 30 (modelOf S.inputCleanup f r) ≠
        (art S.inputCleanup f).base + BitVec.ofNat 64 (4 * k) := by
    simp only [xreg, r_modelOf]; exact hent.raOutside
  obtain ⟨hLok, hU, -⟩ := compileExeU_facts h hB' hF0 hLs hb
  have hgood : L.RunGoodLU M f (modelOf S.inputCleanup f r) := by
    obtain ⟨L0, Ub, envX, XRb, crunX⟩ := L
    change L0 = _ at hLs
    subst hLs
    exact backend_correct_program_budgetUG' _ hLok hU hNI hκ hfm M hent
      (by rw [hκf]; exact ⟨hres, by rw [← hκf M]; exact hκ.2 M f hfm⟩) (by rw [hκf]; rfl)
      (by rw [hκf]; exact hgfree) himg hbe hargs
      hr.entry hsav hrel hpl htr hout
  exact compileExe_correct_unwind_exec_of_good h B hB hf hc M hX ho hr L hLs hb hNI hUS hra1 htr
    (runOkU_of_good hI (codeMap_leanLink hl) hF hH (leanLink_gotSlot hl)
      (fun g hg => destsInt_of_ok hL' hg) hfm hra (runGoodLU_uSys hLs hgood))

/-- **The optimising executable compiler is correct on the exceptional edges, through the
mid-end, on the executable's bytes, for the run's peak call depth**: for
`compileExeOptU S file0 = .ok file`, an outside call of the optimised function `f'` (named `n`)
in `r` with `frameDrop + (D * d + pbMax)` bytes of stack and the hooks' contract `HooksSim`, the linked
program with unwinding `L` of the optimised input with that call's world (its CLIF environment
keeping the link-time symbols), the entry `cs` of the input's function `f` named `n` with the
call's registers, slots and memory, and a bound `d` on the call depth of the optimised program's
run with unwinding: for every fuel `k` the executable machine with unwinding run from `r` refines
the input program's run with unwinding of `k` steps from `cs` (`ExecRefinesU`). -/
theorem compileExeOpt_correct_unwind_exec_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOptU S file0 = .ok file) (B : BaseEnv)
    (hB : BaseOk (sys S.opt.inputCleanup B)) (hH : HooksSim S.opt.inputCleanup B) {n : String}
    {f f' : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f') (d : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs cs' : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (frameDrop (art S.opt.inputCleanup f').af + (S.opt.inputCleanup.D * d + pbMax S.opt.inputCleanup))
      r args cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args cs') (hcs : ClifEntry f args cs)
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem)
    (L : LinkSysU) (hLs : L.toLinkSys = LinkSys.ofInputCleanup S.opt.inputCleanup B
      (worldF S.opt.inputCleanup f' (S.opt.inputCleanup.D * d + pbMax S.opt.inputCleanup) r))
    (hb : BaseU L) (hNI : L.OkUNI) (hkeep : Opt.EnvKeepsSymbolsX L.envX)
    (hUS : UnwSim S.opt.inputCleanup L.Ub) (hra1 : ¬ img S.opt.inputCleanup (xreg 30 r - 1))
    (hd : Clif.DepthLeX L.envX L.P d cs'.toX)
    (htr : ∀ Fu, TrapsExplicitX ((L.peakX Fu).envRX d f') L.P.bare cs')
    (k : Nat) :
    ExecRefinesU (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
      (stepU S.opt.inputCleanup B L.Ub file) r (DeadCleanupBinCheck.RelocAt S.opt.inputCleanup)
      (Clif.runLoopX L.envX (prog S.inputCleanup) k cs.toX) := by
  have hP : L.P = prog S.opt.inputCleanup := by rw [hLs]; rfl
  have hpair : Opt.FunSimU f f' := by
    obtain ⟨g, hg, hfg⟩ := ((funsSimU_prog S).findP (· == n)).1 f hf
    have : (prog S.opt.inputCleanup).func? n = some g := hg
    rw [hf'] at this
    cases this
    exact hfg
  obtain ⟨m, hm⟩ := Opt.runLoopX_refinesU hkeep (funsSimU_prog S) k cs.toX cs'.toX
    (sru_entry hpair hcs hr.entry hregs hsl hmem)
  have hpk := fun Fu => compileExe_correct_unwind_exec_peak h B hB hH hf' Fu d hX ho hr L hLs
    hb hNI hUS hra1 hd (htr Fu)
  rw [← hP] at hm
  cases m with
  | zero =>
    refine execRefinesU_of_outcome hm ?_
    rw [Clif.runLoopX]
    trivial
  | succ Fu => exact execRefinesU_of_outcome hm (hpk Fu)

end Link.DeadCleanup
