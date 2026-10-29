import FV.Link.Exe
import FV.E2E.LegalSource
import FV.E2E.LegalDepth

/-! # The executable compiler refines the original source program (S2, S3)

`Link.compileExe_correct` (`FV/Link/Exe.lean`) relates the executable to `prog S.input`: the
input's functions as `lean-backend` compiles them, after the `i128` legalisation. That program is
the legalisation of the input's **source program** `S.input.srcProg` — the parsed CLIF functions
(`E2E.LinkCheck.LinkInput.prog_eq`). `compileExe` runs no optimiser: its pipeline is the
legalisation followed by the backend (`FnInput.func`, `pipeT`).

**`compileExe_correct_source`**: for `compileExe S file0 = .ok file` and an input in the source
domain (`SrcScopeB`, decided on the parsed functions: each legalisation is the identity or
proven correct, `Opt.Legal.Complete.Pre`), an outside call of the compiled code of a source
function `f` with the ABI-split arguments `args'` of `args` refines the whole-program run of the
**original** program on `args`: a return of the source run is a return of the executable with
the results split by `f`'s return groups (`ExpRel`) in x0.., the same live memory; a trap is the
same trap. It composes the whole-program refinement of the legalisation
(`E2E.LegalProgram.legalProg_refines`) with `compileExe_correct`, no checker premise.

Premises beyond `compileExe_correct`'s (which are taken about the target entry `cs'` and the
legalisation `legalize f`):
* the outside environment's `i128` contracts when a source function mentions `i128`
  (`HelperOk`: `__*ti3` divide; `ExtLegal`: an extern called with split arguments returns split
  results; `EnvKeepsBounded`), and, with indirect calls, no signature known to it (`sigOf`);
* the source entry `cs` (`ClifEntry f args`, the target's slots and memory);
* the source run: its memories have valid ranges below `2^64` (`hbnd`), and, for its traps, no
  load/store traps (`NoMemTrap`): a 16-byte access is two 8-byte accesses after legalisation;
* `TrapsExplicit` of the target run at every fuel (the target fuel is the legalisation's, not
  the source's).

**`compileExe_correct_source_peak`** (L1d): the same for recursive programs — no call-graph
premise; the outside caller provides `frameDrop + (D * d + pbMax)` bytes of stack (#581: `pbMax`,
the stack probes of the deepest activation), where `d` bounds the call
depth of the **source** run (`Clif.DepthLe` of `S.input.srcProg` from `cs`). The legalisation
keeps the call depth (`E2E.LegalProgram.legalProg_refines_depth`), so the legalised run has call
depth at most `d` and `compileExe_correct_peak` applies to it.
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes E2E.LegalProgram Backend
  LinkSpec Opt.Legalize128

/-- The input's program (`prog`) is the legalisation of its source program. -/
theorem prog_eq_legal (I : LinkInput) : prog I = legalProg I.srcProg := by
  rw [← LinkInput.prog_eq]
  simp [prog, progOf, LinkInput.results, LinkInput.prog, Function.comp_def]

/-- Good whole-program states of the source run from bounded memories, no load/store trap, the
symbols kept by the base environment. -/
theorem goodFrom_of {B : Clif.Env} {P : Clif.Program} {G : Prop} {syms : String → Option Nat}
    (hP : ∀ g ∈ P.funcs, Clif.LinkFree g) {s : Clif.State} (hI : Clif.LInv P s)
    (hbnd : ∀ s', Opt.Legal.SReach B P s s' → Opt.Legal.MemBounded s'.mem)
    (hnmt : ∀ s', Opt.Legal.SReach B P s s' → Opt.Legal.MemTrapFree B P s')
    (hsym : G → Opt.EnvKeepsSymbols B ∧ s.mem.symbols = syms) : GoodFrom B P G syms s := by
  intro s' hr
  refine ⟨hbnd s' hr, hnmt s' hr, fun hG => ?_⟩
  obtain ⟨hk, hs⟩ := hsym hG
  suffices ∀ a b, Opt.Legal.SReach B P a b → Clif.LInv P a → b.mem.symbols = a.mem.symbols by
    rw [this s s' hr hI, hs]
  intro a b h
  induction h with
  | refl => exact fun _ => rfl
  | step hs' _ ih =>
    intro hIa
    rw [ih (Clif.step_next_linv hP hIa hs').1, (Clif.step_symbols hP hk hIa).1 _ hs']

/-- **The executable compiler refines the original source program** (S3): for
`compileExe S file0 = .ok file`, a source function `f` of an input in the source domain
(`SrcScopeB`), an outside call of `legalize f`'s code with the ABI-split arguments `args'` (the
premises of `compileExe_correct` about the target entry `cs'`) refines the whole-program run of
the original program from `f`'s entry `cs` on `args`: a return is the executable's return of the
results split by `f`'s return groups with the same memory; a trap (of a source run without
load/store traps, the target runs' traps explicit) is the same trap. -/
theorem compileExe_correct_source {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f)
      (StackBound.stackFn S.input (legalize f)) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
          (step S.input B file) r (RelocAt S.input) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap B.env S.input.srcProg cs → ∀ c,
      Clif.runLoop B.env S.input.srcProg M cs = .trapped c →
      ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
        (step S.input B file) r (RelocAt S.input) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hok := okB_leanLink hin hl
  have hL : (LinkSys.ofInput S.input B fun _ => True).Ok :=
    okB_sound hok (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal S.input
  have hpe' : S.input.prog = prog S.input := by rw [hpe, LinkInput.prog_eq]
  -- the source domain
  have hC : ProgCtx S.input.srcProg B.env (fun n => S.input.syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog S.input).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  -- the entries
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv S.input.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  -- the symbols of the source run (the target entry's, `OutsideCall.symbols`)
  have hsym : SomeInd (legalProg S.input.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.input.syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  -- from the target run of the legalised program to the executable
  have hfP' : legalize f ∈ (prog S.input).funcs := (Clif.Program.func?_some hf').1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (legalProg S.input.srcProg) k cs' = o) →
      o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog S.input) (K + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvN (prog S.input) B.env K) (prog S.input).bare cs') →
      ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
        (step S.input B file) r (RelocAt S.input) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      rw [← hpe] at hk
      have := compileExe_correct h B hB hH hf' hc K hX ho hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env S.input.srcProg (SomeInd (legalProg S.input.srcProg))
        (fun n => S.input.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refines hC hfP hE hG M).1 vals cm hrun
    rw [hst'] at hk
    exact ⟨rv', hrel, hexe _ ⟨k, hk⟩ (fun h => by cases h) fun K hK =>
      trapsExplicit_of_run hL hfP' hcs' ho.symbols hK⟩
  · have hG : GoodFrom B.env S.input.srcProg (SomeInd (legalProg S.input.srcProg))
        (fun n => S.input.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨k, hk⟩ := (legalProg_refines hC hfP hE hG M).2 c hrun
    rw [hst'] at hk
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) fun K _ => htr K

/-- **The executable compiler refines the original source program, recursive programs
included** (S3, L1d): `compileExe_correct_source` without the call-graph premise. The outside
caller of `legalize f`'s code provides `frameDrop + (D * d + pbMax)` bytes of stack (#581: with
the stack probes of the deepest activation), where `d` bounds the
call depth of the **source** run from `cs` (`Clif.DepthLe`: no state the whole-program run of the
original program reaches has more than `d` callers). A return of the source run is the
executable's return of the results split by `f`'s return groups with the same memory; a trap
(of a source run without load/store traps, the target runs' traps explicit under
`Clif.linkEnvD` at every fuel) is the same trap. -/
theorem compileExe_correct_source_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.input = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : S.input.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize f)
      (frameDrop (art S.input (legalize f)).af + (S.input.D * d + pbMax S.input)) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.input.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env S.input.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.input.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
          (step S.input B file) r (RelocAt S.input) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap B.env S.input.srcProg cs → ∀ c,
      Clif.runLoop B.env S.input.srcProg M cs = .trapped c →
      ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
        (step S.input B file) r (RelocAt S.input) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hok := okB_leanLink hin hl
  have hL : (LinkSys.ofInput S.input B fun _ => True).Ok :=
    okB_sound hok (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal S.input
  have hpe' : S.input.prog = prog S.input := by rw [hpe, LinkInput.prog_eq]
  -- the source domain
  have hC : ProgCtx S.input.srcProg B.env (fun n => S.input.syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog S.input).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  -- the entries
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv S.input.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hd' : Clif.DepthLe B.env S.input.srcProg d ⟨cs.frame, [], cs.mem⟩ := by rw [hst]; exact hd
  -- the symbols of the source run (the target entry's, `OutsideCall.symbols`)
  have hsym : SomeInd (legalProg S.input.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => S.input.syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  -- from the target run of the legalised program, of call depth at most `d`, to the executable
  have hfP' : legalize f ∈ (prog S.input).funcs := (Clif.Program.func?_some hf').1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (legalProg S.input.srcProg) k cs' = o) →
      o ≠ .outOfFuel → Clif.DepthLe B.env (prog S.input) d cs' →
      (∀ F, Clif.runLoop B.env (prog S.input) (F + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs') →
      ExecRefines (art S.input (legalize f)).fb (art S.input (legalize f)).base (xreg 30 r)
        (step S.input B file) r (RelocAt S.input) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      rw [← hpe] at hk
      have := compileExe_correct_peak h B hB hH hf' F d hX ho hr hdT (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env S.input.srcProg (SomeInd (legalProg S.input.srcProg))
        (fun n => S.input.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, ⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).1 vals cm hrun
    rw [hst'] at hk hdT
    rw [← hpe] at hdT
    exact ⟨rv', hrel, hexe _ ⟨k, hk⟩ (fun h => by cases h) hdT fun F hF =>
      trapsExplicit_of_runD hL hfP' hcs' ho.symbols hdT hF⟩
  · have hG : GoodFrom B.env S.input.srcProg (SomeInd (legalProg S.input.srcProg))
        (fun n => S.input.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).2 c hrun
    rw [hst'] at hk hdT
    rw [← hpe] at hdT
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) hdT fun F _ => htr F

end Link
