import FV.Link.SemanticExeSourceWith
import FV.Link.SemanticCompileT

/-! # The typed compiler on a Stock route and the original source program (#722)

`attemptT_correct_source`, `attemptT_correct_source_peak`: `attempt_correct_source{,_peak}`
(`FV/Link/SemanticExeSourceWith.lean`) for the typed compiler on a Stock route
`SemanticCompilerWith.attemptT`: about the original (pre-i128-legalisation) program in
`SrcScopeB`, each returned value in the ABI return register of its class (`ExecRefinesT`). The
legalisation, world and foreign-code premises are the integer variants'. -/

set_option autoImplicit false

namespace E2E.SemanticBinary
open Backend Backend.Proof E2E.LinkCheck

/-- `trapsExplicit_of_run` under the typed contract `OkT`. -/
theorem trapsExplicit_of_runTS {L : LinkSys} (hL : L.OkT) {f : Clif.Function} (hf : f ∈ L.P.funcs)
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

/-- `trapsExplicit_of_runD` under the typed contract `OkT`. -/
theorem trapsExplicit_of_runDTS {L : LinkSys} (hL : L.OkT) {f : Clif.Function}
    (hf : f ∈ L.P.funcs)
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

end E2E.SemanticBinary

namespace Link.SemanticCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
variable {lower : ProductionLowering}

/-- **The typed compiler on a Stock route refines the original source program** (S3):
`attempt_correct_source` for `attemptT`, returned values by class (`ExecRefinesT`). -/
theorem attemptT_correct_source {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) (hsrc : SrcScopeB (input lower S true) = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S true) B)) (hH : HooksSim (input lower S true) B)
    (hlegal : (∃ f ∈ (input lower S true).toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S true)).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (input lower S true).toLinkInput.srcProg.func? n = some f)
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S true) (input lower S true).results) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) (legalize f)
      (SemanticStackBound.stackFn (input lower S true) (legalize f)) r args' cs'.mem)
    (hr : ClifRun (input lower S true) B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env (input lower S true).toLinkInput.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (input lower S true).toLinkInput.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S true) (legalize f)).fb
          (art (input lower S true) (legalize f)).base (xreg 30 r)
          (step (input lower S true) B file) r
          (RelocAtWithResults (input lower S true) (input lower S true).results) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S true)) B.env M)
        (prog (input lower S true)).bare cs') →
      Opt.Legal.NoMemTrap B.env (input lower S true).toLinkInput.srcProg cs → ∀ c,
      Clif.runLoop B.env (input lower S true).toLinkInput.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S true) (legalize f)).fb
        (art (input lower S true) (legalize f)).base (xreg 30 r)
        (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := attemptT_spec h
  have hL : (SemanticStackBound.ofInput (input lower S true) B fun _ => True).OkT :=
    SemanticStackBound.okBTS_sound hin (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal (input lower S true)
  have hpe' : (input lower S true).toLinkInput.prog = prog (input lower S true) := by
    rw [hpe, LinkInput.prog_eq]
  have hC : ProgCtx (input lower S true).toLinkInput.srcProg B.env
      (fun n => (input lower S true).syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog (input lower S true)).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv (input lower S true).toLinkInput.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hsym : SomeInd (legalProg (input lower S true).toLinkInput.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => (input lower S true).syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  have hfP' : legalize f ∈ (prog (input lower S true)).funcs := (Clif.Program.func?_some hf').1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (legalProg (input lower S true).toLinkInput.srcProg) k cs' = o) →
      o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog (input lower S true)) (K + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvN (prog (input lower S true)) B.env K)
          (prog (input lower S true)).bare cs') →
      ExecBytes.ExecRefinesT (art (input lower S true) (legalize f)).fb
        (art (input lower S true) (legalize f)).base (xreg 30 r)
        (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      rw [← hpe] at hk
      have := attemptT_correct h B hB hH hf' hc K hX ho hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env (input lower S true).toLinkInput.srcProg
        (SomeInd (legalProg (input lower S true).toLinkInput.srcProg))
        (fun n => (input lower S true).syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, k, hk⟩ := (legalProg_refines hC hfP hE hG M).1 vals cm hrun
    rw [hst'] at hk
    exact ⟨rv', hrel, hexe _ ⟨k, hk⟩ (fun h => by cases h) fun K hK =>
      trapsExplicit_of_runTS hL hfP' hcs' ho.symbols hK⟩
  · have hG : GoodFrom B.env (input lower S true).toLinkInput.srcProg
        (SomeInd (legalProg (input lower S true).toLinkInput.srcProg))
        (fun n => (input lower S true).syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨k, hk⟩ := (legalProg_refines hC hfP hE hG M).2 c hrun
    rw [hst'] at hk
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) fun K _ => htr K

/-- **The typed compiler on a Stock route refines the original source program, recursive
programs included** (S3, L1d): `attempt_correct_source_peak` for `attemptT`, returned values by
class (`ExecRefinesT`); the outside caller provides `frameDrop + (D * d + pbMax)` bytes of stack
(statement change for #581: the stack probes touch up to `pbMax` bytes below the frames). -/
theorem attemptT_correct_source_peak {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) (hsrc : SrcScopeB (input lower S true) = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S true) B)) (hH : HooksSim (input lower S true) B)
    (hlegal : (∃ f ∈ (input lower S true).toLinkInput.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S true)).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (input lower S true).toLinkInput.srcProg.func? n = some f)
    (d : Nat) {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) (legalize f)
      (frameDrop (art (input lower S true) (legalize f)).af +
        ((input lower S true).D * d + pbMax (input lower S true))) r args' cs'.mem)
    (hr : ClifRun (input lower S true) B (legalize f) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env (input lower S true).toLinkInput.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env (input lower S true).toLinkInput.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env (input lower S true).toLinkInput.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S true) (legalize f)).fb
          (art (input lower S true) (legalize f)).base (xreg 30 r)
          (step (input lower S true) B file) r
          (RelocAtWithResults (input lower S true) (input lower S true).results) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S true)) B.env F d)
        (prog (input lower S true)).bare cs') →
      Opt.Legal.NoMemTrap B.env (input lower S true).toLinkInput.srcProg cs → ∀ c,
      Clif.runLoop B.env (input lower S true).toLinkInput.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S true) (legalize f)).fb
        (art (input lower S true) (legalize f)).base (xreg 30 r)
        (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := attemptT_spec h
  have hL : (SemanticStackBound.ofInput (input lower S true) B fun _ => True).OkT :=
    SemanticStackBound.okBTS_sound hin (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal (input lower S true)
  have hpe' : (input lower S true).toLinkInput.prog = prog (input lower S true) := by
    rw [hpe, LinkInput.prog_eq]
  have hC : ProgCtx (input lower S true).toLinkInput.srcProg B.env
      (fun n => (input lower S true).syms.lookup n) :=
    srcCtx hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hfP := (Clif.Program.func?_some hf).1
  have hf' : (prog (input lower S true)).func? n = some (legalize f) := by
    rw [hpe]; exact hC.func?_some hf
  have hcs' := hr.entry
  obtain ⟨b, hb, h2, h3, h4, h5⟩ := hcs.entry
  obtain ⟨b', hb', h2', h3', -, h5'⟩ := hcs'.entry
  have hE : EntryRel f args args' cs.frame cs'.frame :=
    ⟨hcs.func, hcs'.func, ⟨b, hb, h2, h3, h4, h5⟩, ⟨b', hb', h2', h3', h5'⟩, hsl, hexp⟩
  have hst : (⟨cs.frame, [], cs.mem⟩ : Clif.State) = cs := by rw [← hcs.callers]
  have hst' : (⟨cs'.frame, [], cs.mem⟩ : Clif.State) = cs' := by rw [← hcs'.callers, ← hmem]
  have hLe : Clif.LInv (input lower S true).toLinkInput.srcProg cs := by
    rw [← hst]; exact ⟨hE.lframe hfP, fun _ h => nomatch h⟩
  have hd' : Clif.DepthLe B.env (input lower S true).toLinkInput.srcProg d ⟨cs.frame, [], cs.mem⟩ := by
    rw [hst]; exact hd
  have hsym : SomeInd (legalProg (input lower S true).toLinkInput.srcProg) →
      Opt.EnvKeepsSymbols B.env ∧ cs.mem.symbols = fun n => (input lower S true).syms.lookup n := by
    intro hI
    refine ⟨(hC.ind hI).1.keep, ?_⟩
    rw [← hmem]; exact ho.symbols
  have hfP' : legalize f ∈ (prog (input lower S true)).funcs := (Clif.Program.func?_some hf').1
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (legalProg (input lower S true).toLinkInput.srcProg) k cs' = o) →
      o ≠ .outOfFuel → Clif.DepthLe B.env (prog (input lower S true)) d cs' →
      (∀ F, Clif.runLoop B.env (prog (input lower S true)) (F + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvD (prog (input lower S true)) B.env F d)
          (prog (input lower S true)).bare cs') →
      ExecBytes.ExecRefinesT (art (input lower S true) (legalize f)).fb
        (art (input lower S true) (legalize f)).base (xreg 30 r)
        (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      rw [← hpe] at hk
      have := attemptT_correct_peak h B hB hH hf' F d hX ho hr hdT (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have hG : GoodFrom B.env (input lower S true).toLinkInput.srcProg
        (SomeInd (legalProg (input lower S true).toLinkInput.srcProg))
        (fun n => (input lower S true).syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd (memTrapFree_of_returned M cs vals cm hrun) hsym
    rw [← hst] at hrun
    obtain ⟨rv', hrel, ⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).1 vals cm hrun
    rw [hst'] at hk hdT
    rw [← hpe] at hdT
    exact ⟨rv', hrel, hexe _ ⟨k, hk⟩ (fun h => by cases h) hdT fun F hF =>
      trapsExplicit_of_runDTS hL hfP' hcs' ho.symbols hdT hF⟩
  · have hG : GoodFrom B.env (input lower S true).toLinkInput.srcProg
        (SomeInd (legalProg (input lower S true).toLinkInput.srcProg))
        (fun n => (input lower S true).syms.lookup n) ⟨cs.frame, [], cs.mem⟩ := by
      rw [hst]
      exact goodFrom_of hC.free hLe hbnd hnmt hsym
    rw [← hst] at hrun
    obtain ⟨⟨k, hk⟩, hdT⟩ := (legalProg_refines_depth hC hfP hE hG hd' M).2 c hrun
    rw [hst'] at hk hdT
    rw [← hpe] at hdT
    exact hexe _ ⟨k, hk⟩ (fun h => by cases h) hdT fun F _ => htr F

end Link.SemanticCompilerWith
