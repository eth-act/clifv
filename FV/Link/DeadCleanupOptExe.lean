import FV.Link.OptExe
import FV.Link.DeadCleanupExeSource
import FV.Link.ExeInputReachCleanupIn

/-! # The shipped optimising executable compiler is correct (S1, S2, L1)

`Link.DeadCleanup.compileExeOpt` (`FV/Link/OptCompile.lean`): the shipped executable compiler
`Link.DeadCleanup.compileExe` (the backend with the dead-instruction cleanup) on the optimised
input `S.opt` — what `lake exe lean-link --opt` and `cargo fv --lean-link --opt-proven-only`
run. Its theorems are those of the baseline optimising compiler (`FV/Link/OptExe.lean`), about
the cleanup input `S.opt.inputCleanup`: `compileExeOpt_correct`, `compileExeOpt_correct_peak`
(the input's program after legalisation), `compileExeOpt_correct_source`,
`compileExeOpt_correct_source_peak` (the original program), `compileExeOpt_total_reach_input`.
-/

namespace Link.DeadCleanup
set_option autoImplicit false

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128

theorem optRel_prog (S : LinkSpec) : OptRel (prog S.inputCleanup) (prog S.opt.inputCleanup) := by
  rw [prog_eq, prog_eq]; exact S.optRel

theorem compileExeOpt_spec {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) : compileExe S.opt file0 = .ok file := h

/-- The linked system of the optimised input is `Ok`. -/
theorem linkOk_opt {S : LinkSpec} {file0 file : ByteArray} (h : compileExeOpt S file0 = .ok file)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B)) :
    (LinkSys.ofInputCleanup S.opt.inputCleanup B fun _ => True).Ok := by
  obtain ⟨hin, hl⟩ := compileExe_spec (compileExeOpt_spec h)
  exact okBCleanup_sound (okB_leanLink hin hl) (baseOk_F hB) fun _ _ => trivial

/-- The optimised program's run from `cs'` refines the input program's from the input
function's entry `cs` with the same registers, slots and memory. -/
theorem optRun {S : LinkSpec} {B : Clif.Env} (hE : Opt.EnvKeepsSymbols B) {n : String}
    {f f' : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f') {args : List Clif.Val} {cs cs' : Clif.State}
    (hcs : ClifEntry f args cs) (hcs' : ClifEntry f' args cs')
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) (k : Nat) :
    ∃ m, (∀ v cm, Clif.runLoop B (prog S.inputCleanup) k cs = .returned v cm →
        Clif.runLoop B (prog S.opt.inputCleanup) m cs' = .returned v cm) ∧
      (∀ c, Clif.runLoop B (prog S.inputCleanup) k cs = .trapped c →
        Clif.runLoop B (prog S.opt.inputCleanup) m cs' = .trapped c) ∧
      (Opt.Final (Clif.runLoop B (prog S.inputCleanup) k cs) → ∀ d,
        Clif.DepthLe B (prog S.inputCleanup) d cs → Clif.DepthLe B (prog S.opt.inputCleanup) d cs') := by
  have hR := optRel_prog S
  obtain ⟨cs0, hcs0, hr0, hs0, hm0, -, hSR⟩ := hR.entry hf hf' hcs'
  have : cs = cs0 := Link.clifEntry_eq hcs hcs0 (hregs.trans hr0.symm) (hsl.trans hs0.symm)
    (hmem.trans hm0.symm)
  subst this
  exact hR.refines hE hSR k

/-- `ExecRefines` of an outcome of the optimised program's run (`compileExe_correct` at its fuel). -/
theorem execOpt {S : LinkSpec} {file0 file : ByteArray} (h : compileExeOpt S file0 = .ok file)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B)) (hH : HooksSim S.opt.inputCleanup B) {n : String}
    {f' : Clif.Function} (hf' : (prog S.opt.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.opt.inputCleanup S.opt.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args : List Clif.Val} {cs' : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (DeadCleanupStackBound.stackFn S.opt.inputCleanup f') r args cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args cs') {o : Clif.Outcome} {m : Nat}
    (hm : Clif.runLoop B.env (prog S.opt.inputCleanup) m cs' = o) (hof : o ≠ .outOfFuel)
    (htr : ∀ K, Clif.runLoop B.env (prog S.opt.inputCleanup) (K + 1) cs' = o →
      TrapsExplicit (Clif.linkEnvN (prog S.opt.inputCleanup) B.env K) (prog S.opt.inputCleanup).bare cs') :
    ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
      (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) o := by
  cases m with
  | zero => exact absurd hm.symm (by simpa using hof)
  | succ K =>
    have := compileExe_correct (compileExeOpt_spec h) B hB hH hf' hc K hX ho hr (htr K hm)
    rw [hm] at this
    exact this

/-- `ExecRefines` of an outcome of the optimised program's run of call depth at most `d`
(`compileExe_correct_peak` at its fuel). -/
theorem execOptPeak {S : LinkSpec} {file0 file : ByteArray} (h : compileExeOpt S file0 = .ok file)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B)) (hH : HooksSim S.opt.inputCleanup B) {n : String}
    {f' : Clif.Function} (hf' : (prog S.opt.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs' : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (frameDrop (art S.opt.inputCleanup f').af + (S.opt.inputCleanup.D * d + pbMax S.opt.inputCleanup))
      r args cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args cs') (hd : Clif.DepthLe B.env (prog S.opt.inputCleanup) d cs')
    {o : Clif.Outcome} {m : Nat}
    (hm : Clif.runLoop B.env (prog S.opt.inputCleanup) m cs' = o) (hof : o ≠ .outOfFuel)
    (htr : ∀ F, Clif.runLoop B.env (prog S.opt.inputCleanup) (F + 1) cs' = o →
      TrapsExplicit (Clif.linkEnvD (prog S.opt.inputCleanup) B.env F d) (prog S.opt.inputCleanup).bare cs') :
    ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
      (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) o := by
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
    (h : compileExeOpt S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B))
    (hH : HooksSim S.opt.inputCleanup B) (hkeep : Opt.EnvKeepsSymbols B.env) {n : String}
    {f f' : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.opt.inputCleanup S.opt.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (DeadCleanupStackBound.stackFn S.opt.inputCleanup f') r args cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args cs') (hcs : ClifEntry f args cs)
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (prog S.inputCleanup) M cs = .returned vals cm →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.returned vals cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.opt.inputCleanup) B.env K) (prog S.opt.inputCleanup).bare cs') →
      ∀ c, Clif.runLoop B.env (prog S.inputCleanup) M cs = .trapped c →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hcs' := hr.entry
  obtain ⟨m, h1, h2, -⟩ := optRun hkeep hf hf' hcs hcs' hregs hsl hmem M
  have hfP' : f' ∈ (prog S.opt.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · exact execOpt h B hB hH hf' hc hX ho hr (h1 vals cm hrun) (fun h => by cases h)
      fun K hK => trapsExplicit_of_run hL hfP' hcs' ho.symbols hK
  · exact execOpt h B hB hH hf' hc hX ho hr (h2 c hrun) (fun h => by cases h) fun K _ => htr K

/-- **The optimising executable compiler is correct for recursive programs, with the stack of
the run's peak call depth**: `compileExeOpt_correct` without the call-graph premise; the outside
caller provides `frameDrop + (D * d + pbMax)` bytes of stack (#581), where `d` bounds the call depth of the input
program's run from `cs` (the mid-end keeps the call depth of the runs it refines). -/
theorem compileExeOpt_correct_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B))
    (hH : HooksSim S.opt.inputCleanup B) (hkeep : Opt.EnvKeepsSymbols B.env) {n : String}
    {f f' : Clif.Function} (hf : (prog S.inputCleanup).func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (frameDrop (art S.opt.inputCleanup f').af + (S.opt.inputCleanup.D * d + pbMax S.opt.inputCleanup))
      r args cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args cs') (hcs : ClifEntry f args cs)
    (hregs : cs.frame.regs = cs'.frame.regs) (hsl : cs.frame.slots = cs'.frame.slots)
    (hmem : cs.mem = cs'.mem) (hd : Clif.DepthLe B.env (prog S.inputCleanup) d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (prog S.inputCleanup) M cs = .returned vals cm →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.returned vals cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.opt.inputCleanup) B.env F d) (prog S.opt.inputCleanup).bare cs') →
      ∀ c, Clif.runLoop B.env (prog S.inputCleanup) M cs = .trapped c →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hcs' := hr.entry
  obtain ⟨m, h1, h2, h3⟩ := optRun hkeep hf hf' hcs hcs' hregs hsl hmem M
  have hfP' : f' ∈ (prog S.opt.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  refine ⟨fun vals cm hrun => ?_, fun htr c hrun => ?_⟩
  · have hd' := h3 (by rw [hrun]; trivial) d hd
    exact execOptPeak h B hB hH hf' d hX ho hr hd' (h1 vals cm hrun) (fun h => by cases h)
      fun F hF => E2E.Binary.trapsExplicit_of_runD hL hfP' hcs' ho.symbols hd' hF
  · have hd' := h3 (by rw [hrun]; trivial) d hd
    exact execOptPeak h B hB hH hf' d hX ho hr hd' (h2 c hrun) (fun h => by cases h)
      fun F _ => htr F

/-- The source domain's context from the optimised input's linked system. -/
theorem srcCtx_opt {S : LinkSpec} {file0 file : ByteArray} (h : compileExeOpt S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true) (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B))
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none) :
    ProgCtx S.inputCleanup.srcProg B.env (fun n => S.inputCleanup.syms.lookup n) := by
  have hL := linkOk_opt h B hB
  have hR := optRel_prog S
  have hpe' : S.inputCleanup.prog = prog S.inputCleanup := (prog_eq S).symm
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
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B)) (hH : HooksSim S.opt.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.opt.inputCleanup S.opt.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (DeadCleanupStackBound.stackFn S.opt.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
          (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.returned vals' cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.opt.inputCleanup) B.env K) (prog S.opt.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hpe := prog_eq_legal S
  have hC := srcCtx_opt h hsrc B hB hlegal hsig
  have hfP := (Clif.Program.func?_some hf).1
  have hfL : (prog S.inputCleanup).func? n = some (legalize f) := by rw [hpe]; exact hC.func?_some hf
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
  have hLe : Clif.LInv S.inputCleanup.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hsym : SomeInd (legalProg S.inputCleanup.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.inputCleanup.syms.lookup n := by
    intro _
    refine ⟨hkeep, ?_⟩
    rw [← hmem]; exact ho.symbols
  have hfP' : f' ∈ (prog S.opt.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  -- legal run → optimised run
  have hopt : ∀ k, ∃ m, (∀ v cm, Clif.runLoop B.env (legalProg S.inputCleanup.srcProg) k csL =
        .returned v cm → Clif.runLoop B.env (prog S.opt.inputCleanup) m cs' = .returned v cm) ∧
      (∀ c, Clif.runLoop B.env (legalProg S.inputCleanup.srcProg) k csL = .trapped c →
        Clif.runLoop B.env (prog S.opt.inputCleanup) m cs' = .trapped c) := by
    intro k
    obtain ⟨m, h1, h2, -⟩ := optRun hkeep hfL hf' hcsL hcs' hrL hsL hmL k
    exact ⟨m, fun v cm hk => h1 v cm (by rw [hpe]; exact hk), fun c hk => h2 c (by rw [hpe]; exact hk)⟩
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refines hC hfP hE hG M).1 vals cm hrun
    rw [hstL] at hk
    obtain ⟨m, h1, -⟩ := hopt k
    exact ⟨rv', hrel, execOpt h B hB hH hf' hc hX ho hr (h1 _ _ hk) (fun h => by cases h)
      fun K hK => trapsExplicit_of_run hL hfP' hcs' ho.symbols hK⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨k, hk⟩ := (legalProg_refines hC hfP hE hG M).2 c hrun
    rw [hstL] at hk
    obtain ⟨m, -, h2⟩ := hopt k
    exact execOpt h B hB hH hf' hc hX ho hr (h2 _ hk) (fun h => by cases h) fun K _ => htr K

/-- **The optimising executable compiler refines the original source program, recursive
programs included** (S2, S3, L1d): `compileExeOpt_correct_source` without the call-graph
premise; the outside caller provides `frameDrop + (D * d + pbMax)` bytes of stack (#581), where `d` bounds the
call depth of the **source** run (`Clif.DepthLe`): the legalisation and the mid-end keep the
call depth of the runs they refine. -/
theorem compileExeOpt_correct_source_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B)) (hH : HooksSim S.opt.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (frameDrop (art S.opt.inputCleanup f').af + (S.opt.inputCleanup.D * d + pbMax S.opt.inputCleanup))
      r args' cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env S.inputCleanup.srcProg d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
          (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.opt.inputCleanup) B.env F d)
        (prog S.opt.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hpe := prog_eq_legal S
  have hC := srcCtx_opt h hsrc B hB hlegal hsig
  have hfP := (Clif.Program.func?_some hf).1
  have hfL : (prog S.inputCleanup).func? n = some (legalize f) := by rw [hpe]; exact hC.func?_some hf
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
  have hLe : Clif.LInv S.inputCleanup.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hd' : Clif.DepthLe B.env S.inputCleanup.srcProg d ⟨cs.frame, [], cs.mem⟩ := by rw [hst]; exact hd
  have hsym : SomeInd (legalProg S.inputCleanup.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.inputCleanup.syms.lookup n := by
    intro _
    refine ⟨hkeep, ?_⟩
    rw [← hmem]; exact ho.symbols
  have hfP' : f' ∈ (prog S.opt.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  -- legal run (call depth `d`) → optimised run (call depth `d`)
  have hopt : ∀ k, Clif.DepthLe B.env (legalProg S.inputCleanup.srcProg) d csL → ∃ m,
      (∀ v cm, Clif.runLoop B.env (legalProg S.inputCleanup.srcProg) k csL = .returned v cm →
        Clif.runLoop B.env (prog S.opt.inputCleanup) m cs' = .returned v cm ∧
          Clif.DepthLe B.env (prog S.opt.inputCleanup) d cs') ∧
      (∀ c, Clif.runLoop B.env (legalProg S.inputCleanup.srcProg) k csL = .trapped c →
        Clif.runLoop B.env (prog S.opt.inputCleanup) m cs' = .trapped c ∧
          Clif.DepthLe B.env (prog S.opt.inputCleanup) d cs') := by
    intro k hdL
    obtain ⟨m, h1, h2, h3⟩ := optRun hkeep hfL hf' hcsL hcs' hrL hsL hmL k
    rw [← hpe] at hdL
    refine ⟨m, fun v cm hk => ?_, fun c hk => ?_⟩
    · rw [← hpe] at hk
      exact ⟨h1 v cm hk, h3 (by rw [hk]; trivial) d hdL⟩
    · rw [← hpe] at hk
      exact ⟨h2 c hk, h3 (by rw [hk]; trivial) d hdL⟩
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, ⟨k, hk⟩, hdL⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).1 vals cm hrun
    rw [hstL] at hk hdL
    obtain ⟨m, h1, -⟩ := hopt k hdL
    obtain ⟨hm, hdO⟩ := h1 _ _ hk
    exact ⟨rv', hrel, execOptPeak h B hB hH hf' d hX ho hr hdO hm (fun h => by cases h)
      fun F hF => E2E.Binary.trapsExplicit_of_runD hL hfP' hcs' ho.symbols hdO hF⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨⟨k, hk⟩, hdL⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).2 c hrun
    rw [hstL] at hk hdL
    obtain ⟨m, -, h2⟩ := hopt k hdL
    obtain ⟨hm, hdO⟩ := h2 _ hk
    exact execOptPeak h B hB hH hf' d hX ho hr hdO hm (fun h => by cases h) fun F _ => htr F

/-- **The optimising executable compiler succeeds on input conditions decided without
compiling** (`compileExe_total_reach_input` on the optimised input): on the optimised input
(`InScopeIn`), its layout (`layoutOkB`), the reach of its functions' references from the region
(`reachOkB`), rust-lld's executable `file0` (`file0OkB`), with the sizes of the optimised
functions' compiled code. -/
theorem compileExeOpt_total_reach_input {S : LinkSpec} {file0 : ByteArray} {phs : List Phdr}
    (hin : InScopeIn (placed S.opt).input0 = true) (hl : (placed S.opt).layoutOkB = true)
    (hph : phdrs (fileRd file0) = some phs) (hf : (placed S.opt).file0OkB file0 phs = true)
    (hreach : (placed S.opt).reachOkB = true) :
    compileExeOpt (S.withSizes (sizesOf S.opt)) file0 =
      .ok (patch file0 (offsetOf phs S.R) (regionOf (placed S.opt) (tpOff phs))) := by
  show compileExe (S.withSizes (sizesOf S.opt)).opt file0 = _
  rw [Link.withSizes_opt]
  exact compileExe_total_reach_input hin hl hph hf hreach

end Link.DeadCleanup
