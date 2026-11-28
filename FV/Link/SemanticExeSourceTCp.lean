import FV.Link.SemanticExeSourceT
import FV.Link.CpSource

/-! # The typed compiler on a Stock route refines the bundle's program (#1100, audit row A18)

`attemptT_correct_source{,_peak}` (`FV/Link/SemanticExeSourceT.lean`) about the **bundle's
program**, through the `i128` legalisation and constant-phi removal, as
`Link.SemanticCompilerWith.attempt_correct_source{,_peak}Cp` (`FV/Link/SemanticExeSourceCp.lean`)
for the integer attempt: for an input `I0` in `SrcScopeB` whose constant-phi removal is `S`'s
functions (`hcp`), the compiled function `f'` named `f`'s name (`cpSource`, `cpSource_depth`),
returned values by class (`ExecRefinesT`). `attemptT_correct_source` needs the compiled input's
source program in `SrcScopeB`, which constant-phi removal can break (an `i128` function printed
after the legalisation); `lean-link` instantiates this one at `I0 = S0.input0` and the typed Stock
route's placement of `S0.cp` (`hcp`: `TypedStockShared.stockSteps_placed`, then `rfl`).
-/
set_option autoImplicit false
namespace Link.SemanticCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
variable {lower : ProductionLowering}

/-- **The typed compiler on a Stock route refines the bundle's program** (#1100):
`attemptT_correct_source` about the program `I0.srcProg` of an input in the source domain whose
constant-phi removal is the compiled input's functions. For `attemptT lower S file0 = .ok file`, a
source function `f` of `I0`, and an outside call of the code of the compiled function `f'` named
`f`'s name (no call cycle reachable from it) with the ABI-split arguments `args'` of `args`: a
return of `I0`'s source run from `f`'s entry `cs` is the executable's return of the results split
by `f`'s return groups, each in the ABI return register of its class, with the same memory; a trap
(of a source run without load/store traps, the target runs' traps explicit) is the same trap. -/
theorem attemptT_correct_sourceCp {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S true) B))
    (hH : HooksSim (input lower S true) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S true)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog (input lower S true)).func? n = some f')
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S true) (input lower S true).results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) f'
      (SemanticStackBound.stackFn (input lower S true) f') r args' cs'.mem)
    (hr : ClifRun (input lower S true) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
          (xreg 30 r) (step (input lower S true) B file) r
          (RelocAtWithResults (input lower S true) (input lower S true).results)
          (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S true)) B.env M)
        (prog (input lower S true)).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
        (xreg 30 r) (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results)
        (.trapped c)) := by
  obtain ⟨hin, -⟩ := attemptT_spec h
  have hL : (SemanticStackBound.ofInput (input lower S true) B fun _ => True).OkTR :=
    SemanticStackBound.okBTS_soundR hin (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal (input lower S true)
  have hpe' : (input lower S true).toLinkInput.prog = prog (input lower S true) := by
    rw [hpe, LinkInput.prog_eq]
  have hcpI : (input lower S true).toLinkInput.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program
  have hC : ProgCtx I0.srcProg B.env (fun n => (input lower S true).syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hcs' := hr.entry
  have hfI : (input lower S true).toLinkInput.prog.func? n = some f' := by rw [hpe']; exact hf'
  have hfP' : f' ∈ (prog (input lower S true)).funcs := (Clif.Program.func?_some hf').1
  -- the bundle's run → the compiled program's run
  obtain ⟨hret, htrap⟩ := cpSource hcpI hC hkeep hf hfI hcs hcs' hexp hsl hmem
    (fun _ => by rw [← hmem]; exact ho.symbols) hbnd M
  -- the compiled program's run → the executable
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog (input lower S true)) k cs' = o) →
      o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog (input lower S true)) (K + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvN (prog (input lower S true)) B.env K)
          (prog (input lower S true)).bare cs') →
      ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
        (xreg 30 r) (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      have := attemptT_correct h B hB hH hf' hc K hX ho hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, m, hm⟩ := hret vals cm hrun
    rw [hpe'] at hm
    exact ⟨rv', hrel, hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K hK =>
      trapsExplicit_of_runTSR hL hfP' hcs' ho.symbols hK⟩
  · obtain ⟨m, hm⟩ := htrap hnmt c hrun
    rw [hpe'] at hm
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K _ => htr K

/-- **The typed compiler on a Stock route refines the bundle's program, recursive programs
included** (#1100): `attemptT_correct_source_peak` about the program `I0.srcProg` of an input in
the source domain whose constant-phi removal is the compiled input's functions; no call-graph
premise; the outside caller of `f'`'s code provides `frameDrop + (D * d + pbMax)` bytes of stack,
where `d` bounds the call depth of `I0`'s source run from `cs` (`Clif.DepthLe`). Returned values
by class (`ExecRefinesT`). -/
theorem attemptT_correct_source_peakCp {S : LinkSpec} {file0 file : ByteArray}
    (h : attemptT lower S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S true) B))
    (hH : HooksSim (input lower S true) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S true)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog (input lower S true)).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S true) (BinCheck.roByte (input lower S true) S.data) f'
      (frameDrop (art (input lower S true) f').af +
        ((input lower S true).D * d + pbMax (input lower S true))) r args' cs'.mem)
    (hr : ClifRun (input lower S true) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
          (xreg 30 r) (step (input lower S true) B file) r
          (RelocAtWithResults (input lower S true) (input lower S true).results)
          (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S true)) B.env F d)
        (prog (input lower S true)).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
        (xreg 30 r) (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results)
        (.trapped c)) := by
  obtain ⟨hin, -⟩ := attemptT_spec h
  have hL : (SemanticStackBound.ofInput (input lower S true) B fun _ => True).OkTR :=
    SemanticStackBound.okBTS_soundR hin (baseOk_F hB) fun _ _ => trivial
  have hpe := prog_eq_legal (input lower S true)
  have hpe' : (input lower S true).toLinkInput.prog = prog (input lower S true) := by
    rw [hpe, LinkInput.prog_eq]
  have hcpI : (input lower S true).toLinkInput.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program
  have hC : ProgCtx I0.srcProg B.env (fun n => (input lower S true).syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hcs' := hr.entry
  have hfI : (input lower S true).toLinkInput.prog.func? n = some f' := by rw [hpe']; exact hf'
  have hfP' : f' ∈ (prog (input lower S true)).funcs := (Clif.Program.func?_some hf').1
  -- the bundle's run (call depth `d`) → the compiled program's run (call depth `d`)
  obtain ⟨hret, htrap⟩ := cpSource_depth hcpI hC hkeep hf hfI hcs hcs' hexp hsl hmem
    (fun _ => by rw [← hmem]; exact ho.symbols) hbnd hd M
  -- the compiled program's run of call depth at most `d` → the executable
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog (input lower S true)) k cs' = o) →
      o ≠ .outOfFuel → Clif.DepthLe B.env (prog (input lower S true)) d cs' →
      (∀ F, Clif.runLoop B.env (prog (input lower S true)) (F + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvD (prog (input lower S true)) B.env F d)
          (prog (input lower S true)).bare cs') →
      ExecBytes.ExecRefinesT (art (input lower S true) f').fb (art (input lower S true) f').base
        (xreg 30 r) (step (input lower S true) B file) r
        (RelocAtWithResults (input lower S true) (input lower S true).results) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      have := attemptT_correct_peak h B hB hH hf' F d hX ho hr hdT (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, ⟨m, hm⟩, hdT⟩ := hret vals cm hrun
    rw [hpe'] at hm hdT
    exact ⟨rv', hrel, hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F hF =>
      trapsExplicit_of_runDTSR hL hfP' hcs' ho.symbols hdT hF⟩
  · obtain ⟨⟨m, hm⟩, hdT⟩ := htrap hnmt c hrun
    rw [hpe'] at hm hdT
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F _ => htr F

end Link.SemanticCompilerWith
