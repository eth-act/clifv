import FV.Link.ExeSource
import FV.Link.OptFacts
import FV.Link.ExeTotal
import FV.Link.ExeInputReach

/-! # The optimising executable compiler is correct (S1, S2, L1)

`compileExeOpt S file0` (`FV/Link/OptCompile.lean`) is `compileExe` on the optimised input
`S.opt`: its pipeline is parse → `i128` legalisation → mid-end (`Opt.optimizeExe`, the proven
rule sets) → backend. Its theorems compose `compileExe`'s (about the optimised program
`prog S.opt.input`) with the mid-end's whole-program refinement (`OptRel.refines`:
`call_indirect` and `try_call`/`try_call_indirect` included, call depth kept) and, for the
original program, the legalisation's (`E2E.LegalProgram.legalProg_refines{,_depth}`):

* **`compileExeOpt_correct`** (about the input's program `prog S.input`, after legalisation, before
  the mid-end) and **`compileExeOpt_correct_peak`** (recursive programs, the stack of the run's
  peak call depth);
* **`compileExeOpt_correct_source`**, **`compileExeOpt_correct_source_peak`** (about the original,
  pre-legalisation program `S.input.srcProg`, inputs in the source domain `SrcScopeB`);
* **`compileExeOpt_total_reach_input`**: the compiler succeeds on the optimised input's
  conditions decided without compiling (`InScopeIn`), its layout, reach and rust-lld's output.

Premises beyond `compileExe`'s (taken about the optimised input `S.opt.input`, its function
`f'` named `n`, the entry `cs'` of the outside call): the base environment keeps the link-time
symbols (`Opt.EnvKeepsSymbols`, the mid-end's contract), and the entry `cs` of the input's
function (the same registers, slots and memory as `cs'`). A trap is refined when the optimised
program's runs trap explicitly (`TrapsExplicit`, at every fuel: the fuels of the two runs differ).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes E2E.LegalProgram Backend
  LinkSpec Opt.Legalize128

/-- The input's program is its functions (the compiler's results, `progOf_resultsT`). -/
theorem prog_input (S : LinkSpec) : prog S.input = S.input.prog := by
  show progOf S.input.results = _
  rw [S.input_results, progOf_resultsT]

/-- The optimised program and the input's program. -/
theorem optRel_prog (S : LinkSpec) : OptRel (prog S.input) (prog S.opt.input) := by
  rw [prog_input, prog_input]; exact S.optRel

theorem compileExeOpt_spec {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) : compileExe S.opt file0 = .ok file := h

/-- The linked system of the optimised input is `Ok`. -/
theorem linkOk_opt {S : LinkSpec} {file0 file : ByteArray} (h : compileExeOpt S file0 = .ok file)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) :
    (LinkSys.ofInput S.opt.input B fun _ => True).Ok := by
  obtain ⟨hin, hl⟩ := compileExe_spec (compileExeOpt_spec h)
  exact okB_sound (okB_leanLink hin hl) (baseOk_F hB) fun _ _ => trivial

/-- Two entries of `f` with the same registers, slots and memory are the same state. -/
theorem clifEntry_eq {f : Clif.Function} {args args' : List Clif.Val} {cs cs0 : Clif.State}
    (h : ClifEntry f args cs) (h0 : ClifEntry f args' cs0) (hr : cs.frame.regs = cs0.frame.regs)
    (hs : cs.frame.slots = cs0.frame.slots) (hm : cs.mem = cs0.mem) : cs = cs0 := by
  obtain ⟨b, hb, h2, h3, -⟩ := h.entry
  obtain ⟨b0, hb0, h20, h30, -⟩ := h0.entry
  rw [hb] at hb0; cases hb0
  obtain ⟨⟨fu, re, sl, bo, te⟩, ca, me⟩ := cs
  obtain ⟨⟨fu0, re0, sl0, bo0, te0⟩, ca0, me0⟩ := cs0
  have hc := h.callers; have hc0 := h0.callers
  have hf := h.func; have hf0 := h0.func
  simp only at hr hs hm h2 h3 h20 h30 hc hc0 hf hf0
  subst hr hs hm hc hc0 hf hf0
  rw [h2, h3, h20, h30]

/-- The optimised program's run from `cs'` refines the input program's from the input
function's entry `cs` with the same registers, slots and memory. -/
theorem optRun {S : LinkSpec} {B : Clif.Env} (hE : Opt.EnvKeepsSymbols B) {n : String}
    {f f' : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f') {args : List Clif.Val} {cs cs' : Clif.State}
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry f' args cs')
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) (k : Nat) :
    ∃ m, (∀ v cm, Clif.runLoop B (prog S.input) k cs = .returned v cm →
        Clif.runLoop B (prog S.opt.input) m cs' = .returned v cm) ∧
      (∀ c, Clif.runLoop B (prog S.input) k cs = .trapped c →
        Clif.runLoop B (prog S.opt.input) m cs' = .trapped c) ∧
      (Opt.Final (Clif.runLoop B (prog S.input) k cs) → ∀ d,
        Clif.DepthLe B (prog S.input) d cs → Clif.DepthLe B (prog S.opt.input) d cs') := by
  have hR := optRel_prog S
  obtain ⟨cs0, hcs0, hr0, hs0, hm0, -, hSR⟩ := hR.entry hf hf' hcs'
  have : cs = cs0 := clifEntry_eq hcs hcs0 (hregs.trans hr0.symm) (hsl.trans hs0.symm)
    (hmem.trans hm0.symm)
  subst this
  exact hR.refines hE hSR k

/-- `ExecRefines` of an outcome of the optimised program's run (`compileExe_correct` at its fuel). -/
theorem execOpt {S : LinkSpec} {file0 file : ByteArray} (h : compileExeOpt S file0 = .ok file)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) (hH : HooksSim S.opt.input B) {n : String}
    {f' : Clif.Function} (hf' : (prog S.opt.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.opt.input S.opt.input.results) f')
    {r : Arm.ArmState} {args : List Clif.Val} {cs' : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (StackBound.stackFn S.opt.input f') r args cs'.mem)
    (hr : ClifRun S.opt.input B f' r args cs') {o : Clif.Outcome} {m : Nat}
    (hm : Clif.runLoop B.env (prog S.opt.input) m cs' = o) (hof : o ≠ .outOfFuel)
    (htr : ∀ K, Clif.runLoop B.env (prog S.opt.input) (K + 1) cs' = o →
      TrapsExplicit (Clif.linkEnvN (prog S.opt.input) B.env K) (prog S.opt.input).bare cs') :
    ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
      (step S.opt.input B file) r (RelocAt S.opt.input) o := by
  cases m with
  | zero => exact absurd hm.symm (by simpa using hof)
  | succ K =>
    have := compileExe_correct (compileExeOpt_spec h) B hB hH hf' hc K hX ho hr (htr K hm)
    rw [hm] at this
    exact this

/-- `ExecRefines` of an outcome of the optimised program's run of call depth at most `d`
(`compileExe_correct_peak` at its fuel). -/
theorem execOptPeak {S : LinkSpec} {file0 file : ByteArray} (h : compileExeOpt S file0 = .ok file)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) (hH : HooksSim S.opt.input B) {n : String}
    {f' : Clif.Function} (hf' : (prog S.opt.input).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs' : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (frameDrop (art S.opt.input f').af + S.opt.input.D * d) r args cs'.mem)
    (hr : ClifRun S.opt.input B f' r args cs') (hd : Clif.DepthLe B.env (prog S.opt.input) d cs')
    {o : Clif.Outcome} {m : Nat}
    (hm : Clif.runLoop B.env (prog S.opt.input) m cs' = o) (hof : o ≠ .outOfFuel)
    (htr : ∀ F, Clif.runLoop B.env (prog S.opt.input) (F + 1) cs' = o →
      TrapsExplicit (Clif.linkEnvD (prog S.opt.input) B.env F d) (prog S.opt.input).bare cs') :
    ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
      (step S.opt.input B file) r (RelocAt S.opt.input) o := by
  cases m with
  | zero => exact absurd hm.symm (by simpa using hof)
  | succ F =>
    have := compileExe_correct_peak (compileExeOpt_spec h) B hB hH hf' F d hX ho hr hd (htr F hm)
    rw [hm] at this
    exact this

/-- **The optimising executable compiler is correct** (about the input's program, after the
`i128` legalisation, before the mid-end): for `compileExeOpt S file0 = .ok file`, an outside call
of the compiled code of the optimised function `f'` (named `n`; no call cycle reachable from it)
refines the whole-program run of the input's program from the entry `cs` of its function `f`
named `n` with the call's registers, slots and memory: a return is the executable's return of
the same values with the same memory; a trap (the optimised runs' traps explicit) is the same
trap. -/
theorem compileExeOpt_correct {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.opt.input B))
    (hH : HooksSim S.opt.input B) (hkeep : Opt.EnvKeepsSymbols B.env) {n : String}
    {f f' : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.opt.input S.opt.input.results) f')
    {r : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (StackBound.stackFn S.opt.input f') r args cs'.mem)
    (hr : ClifRun S.opt.input B f' r args cs') (hcs : ClifEntry f args cs)
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (prog S.input) M cs = .returned vals cm →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.returned vals cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.opt.input) B.env K) (prog S.opt.input).bare cs') →
      ∀ c, Clif.runLoop B.env (prog S.input) M cs = .trapped c →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hcs' := hr.entry
  obtain ⟨m, h1, h2, -⟩ := optRun hkeep hf hf' hcs hcs' hregs hsl hmem M
  have hfP' : f' ∈ (prog S.opt.input).funcs := (Clif.Program.func?_some hf').1
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · exact execOpt h B hB hH hf' hc hX ho hr (h1 vals cm hrun) (fun h => by cases h)
      fun K hK => trapsExplicit_of_run hL hfP' hcs' ho.symbols hK
  · exact execOpt h B hB hH hf' hc hX ho hr (h2 c hrun) (fun h => by cases h) fun K _ => htr K

/-- **The optimising executable compiler is correct for recursive programs, with the stack of
the run's peak call depth**: `compileExeOpt_correct` without the call-graph premise; the outside
caller provides `frameDrop + D * d` bytes of stack, where `d` bounds the call depth of the input
program's run from `cs` (the mid-end keeps the call depth of the runs it refines). -/
theorem compileExeOpt_correct_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.opt.input B))
    (hH : HooksSim S.opt.input B) (hkeep : Opt.EnvKeepsSymbols B.env) {n : String}
    {f f' : Clif.Function} (hf : (prog S.input).func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (frameDrop (art S.opt.input f').af + S.opt.input.D * d) r args cs'.mem)
    (hr : ClifRun S.opt.input B f' r args cs') (hcs : ClifEntry f args cs)
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) (hd : Clif.DepthLe B.env (prog S.input) d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (prog S.input) M cs = .returned vals cm →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.returned vals cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.opt.input) B.env F d) (prog S.opt.input).bare cs') →
      ∀ c, Clif.runLoop B.env (prog S.input) M cs = .trapped c →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hcs' := hr.entry
  obtain ⟨m, h1, h2, h3⟩ := optRun hkeep hf hf' hcs hcs' hregs hsl hmem M
  have hfP' : f' ∈ (prog S.opt.input).funcs := (Clif.Program.func?_some hf').1
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · have hd' := h3 (by rw [hrun]; trivial) d hd
    exact execOptPeak h B hB hH hf' d hX ho hr hd' (h1 vals cm hrun) (fun h => by cases h)
      fun F hF => trapsExplicit_of_runD hL hfP' hcs' ho.symbols hd' hF
  · have hd' := h3 (by rw [hrun]; trivial) d hd
    exact execOptPeak h B hB hH hf' d hX ho hr hd' (h2 c hrun) (fun h => by cases h)
      fun F _ => htr F

/-- The source domain's context from the optimised input's linked system. -/
theorem srcCtx_opt {S : LinkSpec} {file0 file : ByteArray} (h : compileExeOpt S file0 = .ok file)
    (hsrc : SrcScopeB S.input = true) (B : BaseEnv) (hB : BaseOk (sys S.opt.input B))
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none) :
    ProgCtx S.input.srcProg B.env (fun n => S.input.syms.lookup n) := by
  have hL := linkOk_opt h B hB
  have hR := optRel_prog S
  have hpe' : S.input.prog = prog S.input := (prog_input S).symm
  exact srcCtx hsrc (by rw [hpe']; exact hR.nodup hL.names) (by rw [hpe']; exact hR.free hL.free)
    (by rw [hpe']; exact hR.declSig hL.declSig) (by rw [hpe']; exact hR.indScope hL.indScope)
    hlegal (by rw [hpe']; exact hsig)

/-- **The optimising executable compiler refines the original source program** (S2, S3): for
`compileExeOpt S file0 = .ok file`, a source function `f` of an input in the source domain
(`SrcScopeB`), an outside call of the compiled code of the optimised legalisation `f'` of `f`
(named `n`, no call cycle reachable from it) with the ABI-split arguments `args'` of `args`
refines the whole-program run of the **original** program from `f`'s entry `cs` on `args`: a
return is the executable's return of the results split by `f`'s return groups with the same
memory; a trap (of a source run without load/store traps, the optimised runs' traps explicit) is
the same trap. -/
theorem compileExeOpt_correct_source {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) (hH : HooksSim S.opt.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.opt.input S.opt.input.results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (StackBound.stackFn S.opt.input f') r args' cs'.mem)
    (hr : ClifRun S.opt.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
          (step S.opt.input B file) r (RelocAt S.opt.input) (.returned vals' cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.opt.input) B.env K) (prog S.opt.input).bare cs') →
      Opt.Legal.NoMemTrap B.env S.input.srcProg cs → ∀ c,
      Clif.runLoop B.env S.input.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hpe := prog_eq_legal S.input
  have hC := srcCtx_opt h hsrc B hB hlegal hsig
  have hfP := (Clif.Program.func?_some hf).1
  have hfL : (prog S.input).func? n = some (legalize f) := by rw [hpe]; exact hC.func?_some hf
  -- the entries: the optimised function's `cs'`, the legalisation's `csL`, the source's `cs`
  have hcs' := hr.entry
  obtain ⟨csL, hcsL, hrL, hsL, hmL, -, -⟩ := (optRel_prog S).entry hfL hf' hcs'
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcsL.entry
  have hE : EntryRel f args args' cs.frame csL.frame :=
    ⟨hcs.func, hcsL.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩,
      by rw [hsL, hsl], hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hstL : (⟨csL.frame, [], cs.mem⟩ : Clif.State) = csL := by
    rw [← hcsL.callers, ← hmem, ← hmL]
  have hLe : Clif.LInv S.input.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hsym : SomeInd (legalProg S.input.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.input.syms.lookup n := by
    intro _
    refine ⟨hkeep, ?_⟩
    rw [← hmem]; exact ho.symbols
  have hfP' : f' ∈ (prog S.opt.input).funcs := (Clif.Program.func?_some hf').1
  -- legal run → optimised run
  have hopt : ∀ k, ∃ m, (∀ v cm, Clif.runLoop B.env (legalProg S.input.srcProg) k csL =
        .returned v cm → Clif.runLoop B.env (prog S.opt.input) m cs' = .returned v cm) ∧
      (∀ c, Clif.runLoop B.env (legalProg S.input.srcProg) k csL = .trapped c →
        Clif.runLoop B.env (prog S.opt.input) m cs' = .trapped c) := by
    intro k
    obtain ⟨m, h1, h2, -⟩ := optRun hkeep hfL hf' hcsL hcs' hrL hsL hmL k
    exact ⟨m, fun v cm hk => h1 v cm (by rw [hpe]; exact hk), fun c hk => h2 c (by rw [hpe]; exact hk)⟩
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env S.input.srcProg (SomeInd (legalProg S.input.srcProg))
        (fun n => S.input.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refines hC hfP hE hG M).1 vals cm hrun
    rw [hstL] at hk
    obtain ⟨m, h1, -⟩ := hopt k
    exact ⟨rv', hrel, execOpt h B hB hH hf' hc hX ho hr (h1 _ _ hk) (fun h => by cases h)
      fun K hK => trapsExplicit_of_run hL hfP' hcs' ho.symbols hK⟩
  · have hG : GoodFrom B.env S.input.srcProg (SomeInd (legalProg S.input.srcProg))
        (fun n => S.input.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨k, hk⟩ := (legalProg_refines hC hfP hE hG M).2 c hrun
    rw [hstL] at hk
    obtain ⟨m, -, h2⟩ := hopt k
    exact execOpt h B hB hH hf' hc hX ho hr (h2 _ hk) (fun h => by cases h) fun K _ => htr K

/-- **The optimising executable compiler refines the original source program, recursive
programs included** (S2, S3, L1d): `compileExeOpt_correct_source` without the call-graph
premise; the outside caller provides `frameDrop + D * d` bytes of stack, where `d` bounds the
call depth of the **source** run (`Clif.DepthLe`): the legalisation and the mid-end keep the
call depth of the runs they refine. -/
theorem compileExeOpt_correct_source_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.input B)) (hH : HooksSim S.opt.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hf' : (prog S.opt.input).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.input (BinCheck.roByte S.opt.input S.opt.data) f'
      (frameDrop (art S.opt.input f').af + S.opt.input.D * d) r args' cs'.mem)
    (hr : ClifRun S.opt.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env S.input.srcProg d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
          (step S.opt.input B file) r (RelocAt S.opt.input) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.opt.input) B.env F d)
        (prog S.opt.input).bare cs') →
      Opt.Legal.NoMemTrap B.env S.input.srcProg cs → ∀ c,
      Clif.runLoop B.env S.input.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.input f').fb (art S.opt.input f').base (xreg 30 r)
        (step S.opt.input B file) r (RelocAt S.opt.input) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hpe := prog_eq_legal S.input
  have hC := srcCtx_opt h hsrc B hB hlegal hsig
  have hfP := (Clif.Program.func?_some hf).1
  have hfL : (prog S.input).func? n = some (legalize f) := by rw [hpe]; exact hC.func?_some hf
  have hcs' := hr.entry
  obtain ⟨csL, hcsL, hrL, hsL, hmL, -, -⟩ := (optRel_prog S).entry hfL hf' hcs'
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcsL.entry
  have hE : EntryRel f args args' cs.frame csL.frame :=
    ⟨hcs.func, hcsL.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩,
      by rw [hsL, hsl], hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hstL : (⟨csL.frame, [], cs.mem⟩ : Clif.State) = csL := by
    rw [← hcsL.callers, ← hmem, ← hmL]
  have hLe : Clif.LInv S.input.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hd' : Clif.DepthLe B.env S.input.srcProg d ⟨cs.frame, [], cs.mem⟩ := by rw [hst]; exact hd
  have hsym : SomeInd (legalProg S.input.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.input.syms.lookup n := by
    intro _
    refine ⟨hkeep, ?_⟩
    rw [← hmem]; exact ho.symbols
  have hfP' : f' ∈ (prog S.opt.input).funcs := (Clif.Program.func?_some hf').1
  -- legal run (call depth `d`) → optimised run (call depth `d`)
  have hopt : ∀ k, Clif.DepthLe B.env (legalProg S.input.srcProg) d csL → ∃ m,
      (∀ v cm, Clif.runLoop B.env (legalProg S.input.srcProg) k csL = .returned v cm →
        Clif.runLoop B.env (prog S.opt.input) m cs' = .returned v cm ∧
          Clif.DepthLe B.env (prog S.opt.input) d cs') ∧
      (∀ c, Clif.runLoop B.env (legalProg S.input.srcProg) k csL = .trapped c →
        Clif.runLoop B.env (prog S.opt.input) m cs' = .trapped c ∧
          Clif.DepthLe B.env (prog S.opt.input) d cs') := by
    intro k hdL
    obtain ⟨m, h1, h2, h3⟩ := optRun hkeep hfL hf' hcsL hcs' hrL hsL hmL k
    rw [← hpe] at hdL
    refine ⟨m, fun v cm hk => ?_, fun c hk => ?_⟩
    · rw [← hpe] at hk
      exact ⟨h1 v cm hk, h3 (by rw [hk]; trivial) d hdL⟩
    · rw [← hpe] at hk
      exact ⟨h2 c hk, h3 (by rw [hk]; trivial) d hdL⟩
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env S.input.srcProg (SomeInd (legalProg S.input.srcProg))
        (fun n => S.input.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, ⟨k, hk⟩, hdL⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).1 vals cm hrun
    rw [hstL] at hk hdL
    obtain ⟨m, h1, -⟩ := hopt k hdL
    obtain ⟨hm, hdO⟩ := h1 _ _ hk
    exact ⟨rv', hrel, execOptPeak h B hB hH hf' d hX ho hr hdO hm (fun h => by cases h)
      fun F hF => trapsExplicit_of_runD hL hfP' hcs' ho.symbols hdO hF⟩
  · have hG : GoodFrom B.env S.input.srcProg (SomeInd (legalProg S.input.srcProg))
        (fun n => S.input.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨⟨k, hk⟩, hdL⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).2 c hrun
    rw [hstL] at hk hdL
    obtain ⟨m, -, h2⟩ := hopt k hdL
    obtain ⟨hm, hdO⟩ := h2 _ hk
    exact execOptPeak h B hB hH hf' d hX ho hr hdO hm (fun h => by cases h) fun F _ => htr F

/-- `withSizes` and `opt` commute. -/
theorem withSizes_opt (S : LinkSpec) (z : List Nat) : (S.withSizes z).opt = S.opt.withSizes z := by
  obtain ⟨funcs, names, sizes, outside, data, symNames, R⟩ := S
  simp only [LinkSpec.withSizes, LinkSpec.opt, LinkSpec.mk.injEq, List.map_map, true_and,
    and_true]
  exact List.map_congr_left fun fi _ => fi.opt_pair.2.name.symm

/-- **The optimising executable compiler succeeds on input conditions decided without
compiling** (`compileExe_total_reach` on the optimised input): on the optimised input
(`InScopeIn`), its layout (`layoutOkB`), the reach of its functions' references from the region
(`reachOkB`), rust-lld's executable `file0` (`file0OkB`), with the sizes of the optimised
functions' compiled code. -/
theorem compileExeOpt_total_reach_input {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeIn S.opt.placed.input0 = true) (hl : S.opt.placed.layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : S.opt.placed.file0OkB file0 phs = true)
    (hreach : S.opt.placed.reachOkB = true) :
    compileExeOpt (S.withSizes (sizesOf S.opt)) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf S.opt.placed (tpOff phs))) := by
  show compileExe (S.withSizes (sizesOf S.opt)).opt file0 = _
  rw [withSizes_opt]
  exact compileExe_total_reach hin hl hph hf hreach

end Link
