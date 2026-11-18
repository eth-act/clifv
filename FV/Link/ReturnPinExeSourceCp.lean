import FV.Link.ReturnPinExeSourceWith
import FV.Link.CpSource

/-! # The ABI-aware executable attempt refines the bundle's program (#1052)

`attempt_correct_source{,_peak}` (`FV/Link/ReturnPinExeSourceWith.lean`) are about the source
program of the compiled input `S`. `lean-link` compiles the constant-phi-removed input
(`LinkSpec.cp`), whose source program holds each changed function after the `i128` legalisation:
not the bundle's program, and outside `SrcScopeB` where a changed and an unchanged function meet
at an `i128` signature. Here the same conclusions about the **bundle's program**: for an input
`I0` in `SrcScopeB` whose constant-phi removal is `S`'s functions (`hcp`; in `lean-link`,
`I0 = S0.input0` and `S` the route's placement of `S0.cp`), through the legalisation and
constant-phi removal (`cpSource`, `cpSource_depth`, `FV/Link/CpSource.lean`). The compiled function
`f'` named `f`'s name is `f`'s legalisation, constant-phi-removed where the pass changes it.
-/
set_option autoImplicit false
namespace Link.ReturnPinCompilerWith
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.SemanticBinary E2E.SemanticExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128
variable {lower : ProductionLowering}

/-- **The ABI-aware executable attempt refines the bundle's program** (#1052):
`attempt_correct_source` about the program `I0.srcProg` of an input in the source domain whose
constant-phi removal is the compiled input's functions. For `attempt lower S file0 cleanup = .ok
file`, a source function `f` of `I0`, and an outside call of the code of the compiled function
`f'` named `f`'s name (no call cycle reachable from it) with the ABI-split arguments `args'` of
`args`: a return of `I0`'s source run from `f`'s entry `cs` is the executable's return of the
results split by `f`'s return groups with the same memory; a trap (of a source run without
load/store traps, the target runs' traps explicit) is the same trap. -/
theorem attempt_correct_sourceCp {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog (input lower S cleanup)).func? n = some f')
    (hc : ¬ SemanticStackBound.CycleFrom
      (SemanticStackBound.Calls (input lower S cleanup) (input lower S cleanup).results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f'
      (SemanticStackBound.stackFn (input lower S cleanup) f') r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
          (xreg 30 r) (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
          (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env M)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
        (.trapped c)) := by
  obtain ⟨hin, -⟩ := attempt_spec h
  have hL : (SemanticStackBound.ofInput (input lower S cleanup) B fun _ => True).OkSemanticReturnPins :=
    ReturnPinBinary.okB_sound hin (baseOk_F hB) fun _ _ => trivial
  have hpe := SemanticCompilerWith.prog_eq_legal (input lower S cleanup)
  have hpe' : (input lower S cleanup).toLinkInput.prog = prog (input lower S cleanup) := by
    rw [hpe, LinkInput.prog_eq]
  have hcpI : (input lower S cleanup).toLinkInput.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program
  have hC : ProgCtx I0.srcProg B.env (fun n => (input lower S cleanup).syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hcs' := hr.entry
  have hfI : (input lower S cleanup).toLinkInput.prog.func? n = some f' := by rw [hpe']; exact hf'
  have hfP' : f' ∈ (prog (input lower S cleanup)).funcs := (Clif.Program.func?_some hf').1
  -- the bundle's run → the compiled program's run
  obtain ⟨hret, htrap⟩ := cpSource hcpI hC hkeep hf hfI hcs hcs' hexp hsl hmem
    (fun _ => by rw [← hmem]; exact ho.symbols) hbnd M
  -- the compiled program's run → the executable
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog (input lower S cleanup)) k cs' = o) →
      o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog (input lower S cleanup)) (K + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvN (prog (input lower S cleanup)) B.env K)
          (prog (input lower S cleanup)).bare cs') →
      ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      have := attempt_correct h B hB hH hf' hc K hX ho hr (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, m, hm⟩ := hret vals cm hrun
    rw [hpe'] at hm
    exact ⟨rv', hrel, hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K hK =>
      ReturnPinBinary.trapsExplicit_of_run hL hfP' hcs' ho.symbols hK⟩
  · obtain ⟨m, hm⟩ := htrap hnmt c hrun
    rw [hpe'] at hm
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K _ => htr K

/-- **The ABI-aware executable attempt refines the bundle's program, recursive programs
included** (#1052): `attempt_correct_source_peak` about the program `I0.srcProg` of an input in
the source domain whose constant-phi removal is the compiled input's functions; no call-graph
premise; the outside caller of `f'`'s code provides `frameDrop + (D * d + pbMax)` bytes of stack,
where `d` bounds the call depth of `I0`'s source run from `cs` (`Clif.DepthLe`). A return of the
source run is the executable's return of the results split by `f`'s return groups with the same
memory; a trap (of a source run without load/store traps, the target runs' traps explicit under
`Clif.linkEnvD` at every fuel) is the same trap. -/
theorem attempt_correct_source_peakCp {S : LinkSpec} {cleanup : Bool} {file0 file : ByteArray}
    (h : attempt lower S file0 cleanup = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys (input lower S cleanup) B))
    (hH : HooksSim (input lower S cleanup) B) (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog (input lower S cleanup)).funcs, ¬ Clif.IndFree g) →
      ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog (input lower S cleanup)).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall (input lower S cleanup) (BinCheck.roByte (input lower S cleanup) S.data) f'
      (frameDrop (art (input lower S cleanup) f').af +
        ((input lower S cleanup).D * d + pbMax (input lower S cleanup))) r args' cs'.mem)
    (hr : ClifRun (input lower S cleanup) B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
          (xreg 30 r) (step (input lower S cleanup) B file) r
          (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
          (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d)
        (prog (input lower S cleanup)).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results)
        (.trapped c)) := by
  obtain ⟨hin, -⟩ := attempt_spec h
  have hL : (SemanticStackBound.ofInput (input lower S cleanup) B fun _ => True).OkSemanticReturnPins :=
    ReturnPinBinary.okB_sound hin (baseOk_F hB) fun _ _ => trivial
  have hpe := SemanticCompilerWith.prog_eq_legal (input lower S cleanup)
  have hpe' : (input lower S cleanup).toLinkInput.prog = prog (input lower S cleanup) := by
    rw [hpe, LinkInput.prog_eq]
  have hcpI : (input lower S cleanup).toLinkInput.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program
  have hC : ProgCtx I0.srcProg B.env (fun n => (input lower S cleanup).syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hcs' := hr.entry
  have hfI : (input lower S cleanup).toLinkInput.prog.func? n = some f' := by rw [hpe']; exact hf'
  have hfP' : f' ∈ (prog (input lower S cleanup)).funcs := (Clif.Program.func?_some hf').1
  -- the bundle's run (call depth `d`) → the compiled program's run (call depth `d`)
  obtain ⟨hret, htrap⟩ := cpSource_depth hcpI hC hkeep hf hfI hcs hcs' hexp hsl hmem
    (fun _ => by rw [← hmem]; exact ho.symbols) hbnd hd M
  -- the compiled program's run of call depth at most `d` → the executable
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog (input lower S cleanup)) k cs' = o) →
      o ≠ .outOfFuel → Clif.DepthLe B.env (prog (input lower S cleanup)) d cs' →
      (∀ F, Clif.runLoop B.env (prog (input lower S cleanup)) (F + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvD (prog (input lower S cleanup)) B.env F d)
          (prog (input lower S cleanup)).bare cs') →
      ExecRefines (art (input lower S cleanup) f').fb (art (input lower S cleanup) f').base
        (xreg 30 r) (step (input lower S cleanup) B file) r
        (RelocAtWithResults (input lower S cleanup) (input lower S cleanup).results) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      have := attempt_correct_peak h B hB hH hf' F d hX ho hr hdT (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, ⟨m, hm⟩, hdT⟩ := hret vals cm hrun
    rw [hpe'] at hm hdT
    exact ⟨rv', hrel, hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F hF =>
      ReturnPinBinary.trapsExplicit_of_runD hL hfP' hcs' ho.symbols hdT hF⟩
  · obtain ⟨⟨m, hm⟩, hdT⟩ := htrap hnmt c hrun
    rw [hpe'] at hm hdT
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F _ => htr F

end Link.ReturnPinCompilerWith
