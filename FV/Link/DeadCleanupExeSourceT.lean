import FV.Link.DeadCleanupExeSource
import FV.Link.DeadCleanupExePeakT

/-! # The shipped executable compiler on the typed scope refines the original source program
(S11e6, #419)

`Link.DeadCleanup.compileExe_correct_source` (`FV/Link/DeadCleanupExeSource.lean`) for the typed
input conditions: the cleanup input's program is the legalisation of its source program
(`prog_eq_legal`), so the whole-program refinement of the legalisation
(`E2E.LegalProgram.legalProg_refines`) composes with the typed theorem
`compileExe_correctT` (`InScopePT`, the output checks `OutOkTCleanup`, the Lean linker's output;
returned values by class, `ExecRefinesT`). The source domain's program facts come from the typed
link contract `LinkSys.OkT` (`okBCleanup_soundT`), which has the integer contract's `names`,
`free`, `declSig` and `indScope`.

* `trapsExplicit_of_runT`, `trapsExplicit_of_runDT`: `E2E.DeadCleanupBinary.trapsExplicit_of_run`
  and `E2E.Binary.trapsExplicit_of_runD` from `LinkSys.OkT`;
* **`compileExe_correct_sourceT`**: an entry that reaches no call cycle, for the typed premises;
* **`compileExe_correct_source_peakT`**: any entry, recursive ones included, with
  `frameDrop + (D * d + pbMax)` bytes of stack for the source run's call depth `d` (#581)
  (`compileExe_correct_peakT`, `legalProg_refines_depth`);
* **`compileExeT_correct_source`**, **`compileExeT_correct_source_peak`**: the same for
  `compileExeT S file0 = .ok file` (`compileExe` on `InScopeP`, the typed branch otherwise), the
  source theorems `lean-link --verified` reports for a typed input.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128

/-- A returning whole-program CLIF run of `f` satisfies `TrapsExplicit`
(`E2E.DeadCleanupBinary.trapsExplicit_of_run` for the typed link contract `LinkSys.OkT`). -/
theorem trapsExplicit_of_runT {L : LinkSys} (hL : L.OkT) {f : Clif.Function} (hf : f ∈ L.P.funcs)
    {M : Nat} {args : List Clif.Val} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (hcs : ClifEntry f args cs) (hsym : cs.mem.symbols = L.syms)
    (hrun : Clif.runLoop L.base L.P (M + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvN L.P L.base M) L.P.bare cs := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkN (base := L.base) (syms := L.syms) M hL.names hf hL.free
    (hL.indScope f hf)
    (E := Clif.linkEnvN L.P L.base M) rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    (M + 1) cs (Nat.le_refl _) (runInv_entry hf hcs) hIf
    (fun _ => hsym) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact trapsExplicit_of_returned hm

/-- **The shipped executable compiler on the typed scope refines the original source program**
(`compileExe_correct_source` for `InScopePT`): for `leanLink S file0 = .ok file` on a typed
in-scope input passing the output checks `OutOkTCleanup`, in the source domain (`SrcScopeB`), a
source function `f` whose legalisation reaches no call cycle, an outside call of `legalize f`'s
code with the ABI-split arguments `args'` refines the whole-program run of the original program
from `f`'s entry `cs` on `args`: a return is the executable's return of the results split by `f`'s
return groups with the same memory, each in the ABI return register of its class
(`ExecRefinesT`); a trap (of a source run without load/store traps, the target runs' traps
explicit) is the same trap. -/
theorem compileExe_correct_source_okT {S : LinkSpec} {file0 file : ByteArray}
    (hok : okBCleanupT S.inputCleanup = true) (h : leanLink S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
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
        ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).OkT :=
    okBCleanup_soundT hok (baseOk_F hB) fun _ _ => trivial
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
      ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      rw [← hpe] at hk
      have := binary_correct_exec_provenT hok (codeMap_leanLink h) (binOk_leanLink h)
        (gotOk_leanLink h) B hB hH hf' hc K hX ho (outsideAvoids_leanLink h _ _ _ _ _) hr
        (htr K hk)
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
      trapsExplicit_of_runT hL hfP' hcs' ho.symbols hK⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨k, hk⟩ := (legalProg_refines hC hfP hE hG M).2 c hrun
    rw [hst'] at hk
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) fun K _ => htr K

theorem compileExe_correct_sourceT {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopePT S.inputCleanup = true) (hout : OutOkTCleanup S.inputCleanup = true)
    (h : leanLink S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
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
        ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) :=
  compileExe_correct_source_okT (okBT_leanLink hin hout h) h hsrc B hB hH hlegal hsig hf hc hX ho
    hr hcs hexp hsl hmem hbnd M

/-- **`compileExeT` refines the original source program** (`compileExe_correct_source` for the
typed scope): for `compileExeT S file0 = .ok file` (`compileExe` on `InScopeP`, otherwise the
typed premises of `compileExe_correctT`), the conclusion of `compileExe_correct_sourceT`. -/
theorem compileExeT_correct_source {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
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
        ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  rcases compileExeT_spec h with hc0 | ⟨hin, hout, hl⟩ | ⟨hI, hl⟩
  · obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe hc0
    exact compileExe_correct_sourceT hin hout hl hsrc B hB hH hlegal hsig hf hc hX ho hr hcs hexp
      hsl hmem hbnd M
  · exact compileExe_correct_sourceT hin hout hl hsrc B hB hH hlegal hsig hf hc hX ho hr hcs hexp
      hsl hmem hbnd M
  · exact compileExe_correct_source_okT hI hl hsrc B hB hH hlegal hsig hf hc hX ho hr hcs hexp hsl
      hmem hbnd M

/-- A returning whole-program CLIF run of `f` of call depth at most `d` satisfies
`TrapsExplicit` under `Clif.linkEnvD` (`E2E.Binary.trapsExplicit_of_runD` for the typed link
contract `LinkSys.OkT`). -/
theorem trapsExplicit_of_runDT {L : LinkSys} (hL : L.OkT) {f : Clif.Function} (hf : f ∈ L.P.funcs)
    {F d : Nat} {args : List Clif.Val} {cs : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (hcs : ClifEntry f args cs) (hsym : cs.mem.symbols = L.syms)
    (hd : Clif.DepthLe L.base L.P d cs)
    (hrun : Clif.runLoop L.base L.P (F + 1) cs = .returned vals cm) :
    TrapsExplicit (Clif.linkEnvD L.P L.base F d) L.P.bare cs := by
  have hIf : Clif.LInv (L.P.only f) cs := runInv_entry (by simp [Clif.Program.only]) hcs
  obtain ⟨m, hm⟩ := Clif.runLoop_linkD (base := L.base) (syms := L.syms) F d hL.names hf hL.free
    (hL.indScope f hf)
    (E := Clif.linkEnvD L.P L.base F d) rfl rfl (fun _ _ => rfl) (fun _ _ _ => rfl)
    (F + 1) cs (Nat.le_refl _) hd (runInv_entry hf hcs) hIf
    (fun _ => hsym) (by rw [hrun]; exact fun _ h => nomatch h)
    (by rw [hrun]; exact fun h => nomatch h)
  rw [hrun] at hm
  exact trapsExplicit_of_returned hm

/-- **The shipped executable compiler on the typed scope refines the original source program,
recursive programs included** (`compileExe_correct_source_peak` for `InScopePT`): no call-graph
premise; the outside caller of `legalize f`'s code provides `frameDrop + (D * d + pbMax)` bytes of stack,
where `d` bounds the call depth of the **source** run from `cs` (`Clif.DepthLe`). A return of the
source run is the executable's return of the results split by `f`'s return groups with the same
memory, each in the ABI return register of its class (`ExecRefinesT`); a trap (of a source run
without load/store traps, the target runs' traps explicit under `Clif.linkEnvD` at every fuel) is
the same trap. -/
theorem compileExe_correct_source_peak_okT {S : LinkSpec} {file0 file : ByteArray}
    (hok : okBCleanupT S.inputCleanup = true) (h : leanLink S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
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
        ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).OkT :=
    okBCleanup_soundT hok (baseOk_F hB) fun _ _ => trivial
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
      ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      rw [← hpe] at hk
      have := binary_correct_exec_peak_provenT hok (codeMap_leanLink h) (binOk_leanLink h)
        (gotOk_leanLink h) B hB hH hf' F d hX ho (outsideAvoids_leanLink h _ _ _ _ _) hr hdT
        (htr F hk)
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
      trapsExplicit_of_runDT hL hfP' hcs' ho.symbols hdT hF⟩
  · have hG : GoodFrom B.env S.inputCleanup.srcProg (SomeInd (legalProg S.inputCleanup.srcProg))
        (fun n => S.inputCleanup.syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).2 c hrun
    rw [hst'] at hk hdT
    rw [← hpe] at hdT
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) hdT fun F _ => htr F

/-- **The shipped executable compiler on the typed scope refines the original source program,
recursive programs included** (`compileExe_correct_source_peak` for `InScopePT`): no call-graph
premise; the outside caller of `legalize f`'s code provides `frameDrop + (D * d + pbMax)` bytes of stack,
where `d` bounds the call depth of the **source** run from `cs` (`Clif.DepthLe`). A return of the
source run is the executable's return of the results split by `f`'s return groups with the same
memory, each in the ABI return register of its class (`ExecRefinesT`); a trap (of a source run
without load/store traps, the target runs' traps explicit under `Clif.linkEnvD` at every fuel) is
the same trap. -/
theorem compileExe_correct_source_peakT {S : LinkSpec} {file0 file : ByteArray}
    (hin : InScopePT S.inputCleanup = true) (hout : OutOkTCleanup S.inputCleanup = true)
    (h : leanLink S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
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
        ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) :=
  compileExe_correct_source_peak_okT (okBT_leanLink hin hout h) h hsrc B hB hH hlegal hsig hf d hX
    ho hr hcs hexp hsl hmem hbnd hd M

/-- **`compileExeT` refines the original source program, recursive programs included**
(`compileExe_correct_source_peak` for the typed scope): for `compileExeT S file0 = .ok file`, the
conclusion of `compileExe_correct_source_peakT`. -/
theorem compileExeT_correct_source_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
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
        ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  rcases compileExeT_spec h with hc0 | ⟨hin, hout, hl⟩ | ⟨hI, hl⟩
  · obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe hc0
    exact compileExe_correct_source_peakT hin hout hl hsrc B hB hH hlegal hsig hf d hX ho hr hcs
      hexp hsl hmem hbnd hd M
  · exact compileExe_correct_source_peakT hin hout hl hsrc B hB hH hlegal hsig hf d hX ho hr hcs
      hexp hsl hmem hbnd hd M
  · exact compileExe_correct_source_peak_okT hI hl hsrc B hB hH hlegal hsig hf d hX ho hr hcs hexp
      hsl hmem hbnd hd M

end Link.DeadCleanup
