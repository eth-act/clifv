import FV.Link.DeadCleanupExePeak
import FV.Link.ExeSource

/-! # The shipped executable compiler refines the original source program (S3, L1d)

`Link.compileExe_correct_source` and `Link.compileExe_correct_source_peak` relate the baseline
compiler's executable to the **original** (pre-`i128`-legalisation) program. Here the same for
the compiler that `lake exe lean-link` and `cargo fv --lean-link` run by default,
`Link.DeadCleanup.compileExe`: its program `prog S.inputCleanup` (the cleanup pipeline compiles the
same CLIF functions, `progOf_resultsCleanupT`) is the legalisation of the input's source program
(`prog_eq_legal`), so the whole-program refinement of the legalisation
(`E2E.LegalProgram.legalProg_refines`, `legalProg_refines_depth`) composes with the cleanup
compiler's theorems (`compileExe_correct`, `compileExe_correct_peak`).

* **`compileExe_correct_source`**: an entry that reaches no call cycle (stack bound
  `DeadCleanupStackBound.stackFn`);
* **`compileExe_correct_source_peak`**: any entry, recursive ones included, with
  `frameDrop + (D * d + pbMax)` bytes of stack for the source run's call depth `d` (#581: with the
  stack probes of the deepest activation).

The premises are those of the baseline theorems, about the cleanup input `S.inputCleanup`.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128

/-- The cleanup input's program is its CLIF functions. -/
theorem prog_eq (S : LinkSpec) : prog S.inputCleanup = S.inputCleanup.prog := by
  show progOf S.inputCleanup.resultsCleanup = _
  rw [S.inputCleanup_results, progOf_resultsCleanupT]

/-- The cleanup input's program (`prog`) is the legalisation of its source program. -/
theorem prog_eq_legal (S : LinkSpec) : prog S.inputCleanup = legalProg S.inputCleanup.srcProg := by
  rw [prog_eq, LinkInput.prog_eq]

/-- **The shipped executable compiler refines the original source program** (S3):
`Link.compileExe_correct_source` for `Link.DeadCleanup.compileExe`. For an input in the source
domain (`SrcScopeB`), a source function `f` whose legalisation reaches no call cycle, an outside
call of `legalize f`'s code with the ABI-split arguments `args'` refines the whole-program run of
the original program from `f`'s entry `cs` on `args`: a return is the executable's return of the
results split by `f`'s return groups with the same memory; a trap (of a source run without
load/store traps, the target runs' traps explicit) is the same trap. -/
theorem compileExe_correct_source {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize f)
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize f)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hok := okB_leanLink hin hl
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).Ok :=
    okBCleanup_sound hok (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal S
  have hpe' : S.inputCleanup.prog = prog S.inputCleanup := (prog_eq S).symm
  -- the source domain
  have hC : ProgCtx S.inputCleanup.srcProg B.env (fun n => S.inputCleanup.syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog S.inputCleanup).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  -- the entries
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv S.inputCleanup.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  -- the symbols of the source run (the target entry's, `OutsideCall.symbols`)
  have hsym : SomeInd (legalProg S.inputCleanup.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.inputCleanup.syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  -- from the target run of the legalised program to the executable
  have hfP' : legalize f ∈ (prog S.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (legalProg S.inputCleanup.srcProg) k cs' = o) →
      o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog S.inputCleanup) (K + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env K)
          (prog S.inputCleanup).bare cs') →
      ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      rw [← hpe] at hk
      have := compileExe_correct h B hB hH hf' hc K hX ho hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refines hC hfP hE hG M).1 vals cm hrun
    rw [hst'] at hk
    exact ⟨rv', hrel, hexe _ ⟨k, hk⟩ (fun h => by cases h) fun K hK =>
      trapsExplicit_of_run hL hfP' hcs' ho.symbols hK⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨k, hk⟩ := (legalProg_refines hC hfP hE hG M).2 c hrun
    rw [hst'] at hk
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) fun K _ => htr K

/-- **The shipped executable compiler refines the original source program, recursive programs
included** (S3, L1d): `Link.compileExe_correct_source_peak` for `Link.DeadCleanup.compileExe`.
No call-graph premise; the outside caller of `legalize f`'s code provides
`frameDrop + (D * d + pbMax)` (#581: with the stack probes of the deepest activation)
bytes of stack, where `d` bounds the call depth of the **source** run from `cs`
(`Clif.DepthLe`). A return of the source run is the executable's return of the results split by
`f`'s return groups with the same memory; a trap (of a source run without load/store traps, the
target runs' traps explicit under `Clif.linkEnvD` at every fuel) is the same trap. -/
theorem compileExe_correct_source_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.inputCleanup.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize f)
      (frameDrop (art S.inputCleanup (legalize f)).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env S.inputCleanup.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hok := okB_leanLink hin hl
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).Ok :=
    okBCleanup_sound hok (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal S
  have hpe' : S.inputCleanup.prog = prog S.inputCleanup := (prog_eq S).symm
  -- the source domain
  have hC : ProgCtx S.inputCleanup.srcProg B.env (fun n => S.inputCleanup.syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog S.inputCleanup).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  -- the entries
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv S.inputCleanup.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hd' : Clif.DepthLe B.env S.inputCleanup.srcProg d ⟨cs.frame, [], cs.mem⟩ := by
    rw [hst]; exact hd
  -- the symbols of the source run (the target entry's, `OutsideCall.symbols`)
  have hsym : SomeInd (legalProg S.inputCleanup.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.inputCleanup.syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  -- from the target run of the legalised program, of call depth at most `d`, to the executable
  have hfP' : legalize f ∈ (prog S.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (legalProg S.inputCleanup.srcProg) k cs' = o) →
      o ≠ .outOfFuel → Clif.DepthLe B.env (prog S.inputCleanup) d cs' →
      (∀ F, Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
          (prog S.inputCleanup).bare cs') →
      ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      rw [← hpe] at hk
      have := compileExe_correct_peak h B hB hH hf' F d hX ho hr hdT (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, ⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).1 vals cm hrun
    rw [hst'] at hk hdT
    rw [← hpe] at hdT
    exact ⟨rv', hrel, hexe _ ⟨k, hk⟩ (fun h => by cases h) hdT fun F hF =>
      E2E.Binary.trapsExplicit_of_runD hL hfP' hcs' ho.symbols hdT hF⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).2 c hrun
    rw [hst'] at hk hdT
    rw [← hpe] at hdT
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) hdT fun F _ => htr F

end Link.DeadCleanup
