import FV.Link.SemanticExeSourceT
import FV.Link.TypedCompileModes

set_option autoImplicit false

namespace Link.TypedCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
open Link.SemanticCompilerWith
variable {lower : ProductionLowering}

/-- **The typed compiler on a Stock route refines the original source program** (S3):
`attempt_correct_source` for `attempt`, returned values by class (`ExecRefinesT`). -/
theorem attempt_correct_source {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (hsrc : SrcScopeB (input lower S cleanup) = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B)) (hH : HooksSim (input lower S cleanup) B)
    (hlegal : (∃ f ∈ (input lower S cleanup).toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (input lower S cleanup).toLinkInput.srcProg.func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S cleanup) (input lower S cleanup).results) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) (legalize f)
      (SemanticStackBound.stackFn (input lower S cleanup) (legalize f)) r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env (input lower S cleanup).toLinkInput.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (input lower S cleanup).toLinkInput.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S cleanup) (legalize f)).fb
          (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
          (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env (input lower S cleanup).toLinkInput.srcProg cs → ∀ c,
      Clif.runLoop B.env (input lower S cleanup).toLinkInput.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S cleanup) (legalize f)).fb
        (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
        (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := attempt_spec h
  have hL : (SemanticStackBound.ofInput (input lower S cleanup) B fun _ => True).OkT :=
    SemanticStackBound.okBTS_sound hin (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal (input lower S cleanup)
  have hpe' : (input lower S cleanup).toLinkInput.prog = prog (input lower S cleanup) := by
    rw [hpe, LinkInput.prog_eq]
  have hC : ProgCtx (input lower S cleanup).toLinkInput.srcProg B.env
      (fun n => (input lower S cleanup).syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog (input lower S cleanup)).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv (input lower S cleanup).toLinkInput.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hsym : SomeInd (legalProg (input lower S cleanup).toLinkInput.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => (input lower S cleanup).syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  have hfP' : legalize f ∈ (prog (input lower S cleanup)).funcs := (Clif.Program.func?_some hf').1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (legalProg (input lower S cleanup).toLinkInput.srcProg) k cs' = o) →
      o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog (input lower S cleanup)) (K + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env K)
          (prog (input lower S cleanup)).bare cs') →
      ExecBytes.ExecRefinesT (art (input lower S cleanup) (legalize f)).fb
        (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
        (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      rw [← hpe] at hk
      have := attempt_correct h B hB hH hf' hc K hX ho hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env (input lower S cleanup).toLinkInput.srcProg
        (SomeInd (legalProg (input lower S cleanup).toLinkInput.srcProg))
        (fun n => (input lower S cleanup).syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refines hC hfP hE hG M).1 vals cm hrun
    rw [hst'] at hk
    exact ⟨rv', hrel, hexe _ ⟨k, hk⟩ (fun h => by cases h) fun K hK =>
      trapsExplicit_of_runTS hL hfP' hcs' ho.symbols hK⟩
  · have hG : GoodFrom B.env (input lower S cleanup).toLinkInput.srcProg
        (SomeInd (legalProg (input lower S cleanup).toLinkInput.srcProg))
        (fun n => (input lower S cleanup).syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨k, hk⟩ := (legalProg_refines hC hfP hE hG M).2 c hrun
    rw [hst'] at hk
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) fun K _ => htr K

/-- **The typed compiler on a Stock route refines the original source program, recursive
programs included** (S3, L1d): `attempt_correct_source_peak` for `attempt`, returned values by
class (`ExecRefinesT`). -/
theorem attempt_correct_source_peak {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) (hsrc : SrcScopeB (input lower S cleanup) = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B)) (hH : HooksSim (input lower S cleanup) B)
    (hlegal : (∃ f ∈ (input lower S cleanup).toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (input lower S cleanup).toLinkInput.srcProg.func? n = some f)
    (d : Nat) {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) (legalize f)
      (frameDrop (art (input lower S cleanup) (legalize f)).af + (input lower S cleanup).D * d) r args'
        cs'.mem)
    (hr : ClifRun (input lower S cleanup) B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env (input lower S cleanup).toLinkInput.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env (input lower S cleanup).toLinkInput.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (input lower S cleanup).toLinkInput.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S cleanup) (legalize f)).fb
          (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
          (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env (input lower S cleanup).toLinkInput.srcProg cs → ∀ c,
      Clif.runLoop B.env (input lower S cleanup).toLinkInput.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S cleanup) (legalize f)).fb
        (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
        (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := attempt_spec h
  have hL : (SemanticStackBound.ofInput (input lower S cleanup) B fun _ => True).OkT :=
    SemanticStackBound.okBTS_sound hin (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal (input lower S cleanup)
  have hpe' : (input lower S cleanup).toLinkInput.prog = prog (input lower S cleanup) := by
    rw [hpe, LinkInput.prog_eq]
  have hC : ProgCtx (input lower S cleanup).toLinkInput.srcProg B.env
      (fun n => (input lower S cleanup).syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog (input lower S cleanup)).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv (input lower S cleanup).toLinkInput.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hd' : Clif.DepthLe B.env (input lower S cleanup).toLinkInput.srcProg d ⟨cs.frame, [], cs.mem⟩ := by
    rw [hst]; exact hd
  have hsym : SomeInd (legalProg (input lower S cleanup).toLinkInput.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => (input lower S cleanup).syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  have hfP' : legalize f ∈ (prog (input lower S cleanup)).funcs := (Clif.Program.func?_some hf').1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (legalProg (input lower S cleanup).toLinkInput.srcProg) k cs' = o) →
      o ≠ .outOfFuel → Clif.DepthLe B.env (prog (input lower S cleanup)) d cs' →
      (∀ F, Clif.runLoop B.env (prog (input lower S cleanup)) (F + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d)
          (prog (input lower S cleanup)).bare cs') →
      ExecBytes.ExecRefinesT (art (input lower S cleanup) (legalize f)).fb
        (art (input lower S cleanup) (legalize f)).base (xreg 30 r)
        (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      rw [← hpe] at hk
      have := attempt_correct_peak h B hB hH hf' F d hX ho hr hdT (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env (input lower S cleanup).toLinkInput.srcProg
        (SomeInd (legalProg (input lower S cleanup).toLinkInput.srcProg))
        (fun n => (input lower S cleanup).syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, ⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).1 vals cm hrun
    rw [hst'] at hk hdT
    rw [← hpe] at hdT
    exact ⟨rv', hrel, hexe _ ⟨k, hk⟩ (fun h => by cases h) hdT fun F hF =>
      trapsExplicit_of_runDTS hL hfP' hcs' ho.symbols hdT hF⟩
  · have hG : GoodFrom B.env (input lower S cleanup).toLinkInput.srcProg
        (SomeInd (legalProg (input lower S cleanup).toLinkInput.srcProg))
        (fun n => (input lower S cleanup).syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).2 c hrun
    rw [hst'] at hk hdT
    rw [← hpe] at hdT
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) hdT fun F _ => htr F

end Link.TypedCompilerWith
