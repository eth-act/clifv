import FV.Link.ExeSource
import FV.Link.CpSource

/-! # The executable compiler refines the bundle's program (#1052)

`compileExe_correct_source{,_peak}` (`FV/Link/ExeSource.lean`) about the **bundle's program**
through the `i128` legalisation and constant-phi removal, as
`Link.ReturnPinCompilerWith.attempt_correct_source{,_peak}Cp` (`FV/Link/ReturnPinExeSourceCp.lean`,
which says why): for an input `I0` in `SrcScopeB` whose constant-phi removal is `S`'s functions
(`hcp`), the compiled function `f'` named `f`'s name (`cpSource`, `cpSource_depth`).
-/

namespace Link

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes E2E.LegalProgram Backend
  LinkSpec Opt.Legalize128

/-- **The executable compiler refines the bundle's program** (#1052):
`compileExe_correct_source` about the program `I0.srcProg` of an input in the source domain whose constant-phi removal is the compiled input's functions (`hcp`; in `lean-link`, `I0 = S0.input0` and `S` the
placement of `S0.cp`). For `compileExe S file0 = .ok file`, a source function `f` of `I0`,
and an outside call of the code of the compiled function `f'` named `f`'s name (no call cycle
reachable from it) with the ABI-split arguments `args'` of `args`: a return of `I0`'s source run
from `f`'s entry `cs` is the executable's return of the results split by `f`'s return groups with
the same memory; a trap (of a source run without load/store traps, the target runs' traps
explicit) is the same trap. -/
theorem compileExe_correct_sourceCp {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog S.input).func? n = some f')
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f'
      (StackBound.stackFn S.input f') r args' cs'.mem)
    (hr : ClifRun S.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input f').fb (art S.input f').base
          (xreg 30 r) (step S.input B file) r (RelocAt S.input) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.input f').fb (art S.input f').base
        (xreg 30 r) (step S.input B file) r (RelocAt S.input) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hL : (LinkSys.ofInput S.input B fun _ => True).Ok :=
    okB_sound (okB_leanLink hin hl) (baseOk_F hB) fun _ _ => trivial
  have hpe' : S.input.prog = prog S.input := by rw [prog_eq_legal S.input, LinkInput.prog_eq]
  have hcpI : S.input.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program
  have hC : ProgCtx I0.srcProg B.env (fun n => S.input.syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hcs' := hr.entry
  have hfI : S.input.prog.func? n = some f' := by rw [hpe']; exact hf'
  have hfP' : f' ∈ (prog S.input).funcs := (Clif.Program.func?_some hf').1
  -- the bundle's run → the compiled program's run
  obtain ⟨hret, htrap⟩ := cpSource hcpI hC hkeep hf hfI hcs hcs' hexp hsl hmem
    (fun _ => by rw [← hmem]; exact ho.symbols) hbnd M
  -- the compiled program's run → the executable
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog S.input) k cs' = o) →
      o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog S.input) (K + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvN (prog S.input) B.env K) (prog S.input).bare cs') →
      ExecRefines (art S.input f').fb (art S.input f').base
        (xreg 30 r) (step S.input B file) r (RelocAt S.input) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      have := compileExe_correct h B hB hH hf' hc K hX ho hr
        (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, m, hm⟩ := hret vals cm hrun
    rw [hpe'] at hm
    exact ⟨rv', hrel, hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K hK =>
      trapsExplicit_of_run hL hfP' hcs' ho.symbols hK⟩
  · obtain ⟨m, hm⟩ := htrap hnmt c hrun
    rw [hpe'] at hm
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K _ => htr K

/-- **The executable compiler refines the bundle's program, recursive programs included** (#1052):
`compileExe_correct_source_peak` about the program `I0.srcProg` of an input in the source domain whose constant-phi removal is the compiled input's functions; no
call-graph premise; the outside caller of `f'`'s code provides `frameDrop + (D * d + pbMax)` bytes
of stack, where `d` bounds the call depth of `I0`'s source run from `cs` (`Clif.DepthLe`). A
return of the source run is the executable's return of the results split by `f`'s return groups
with the same memory; a trap (of a source run without load/store traps, the target runs'
traps explicit under `Clif.linkEnvD` at every fuel) is the same trap. -/
theorem compileExe_correct_source_peakCp {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog S.input).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) f'
      (frameDrop (art S.input f').af + (S.input.D * d + pbMax S.input)) r args' cs'.mem)
    (hr : ClifRun S.input B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input f').fb (art S.input f').base
          (xreg 30 r) (step S.input B file) r (RelocAt S.input) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.input f').fb (art S.input f').base
        (xreg 30 r) (step S.input B file) r (RelocAt S.input) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  have hL : (LinkSys.ofInput S.input B fun _ => True).Ok :=
    okB_sound (okB_leanLink hin hl) (baseOk_F hB) fun _ _ => trivial
  have hpe' : S.input.prog = prog S.input := by rw [prog_eq_legal S.input, LinkInput.prog_eq]
  have hcpI : S.input.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program
  have hC : ProgCtx I0.srcProg B.env (fun n => S.input.syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hcs' := hr.entry
  have hfI : S.input.prog.func? n = some f' := by rw [hpe']; exact hf'
  have hfP' : f' ∈ (prog S.input).funcs := (Clif.Program.func?_some hf').1
  -- the bundle's run (call depth `d`) → the compiled program's run (call depth `d`)
  obtain ⟨hret, htrap⟩ := cpSource_depth hcpI hC hkeep hf hfI hcs hcs' hexp hsl hmem
    (fun _ => by rw [← hmem]; exact ho.symbols) hbnd hd M
  -- the compiled program's run of call depth at most `d` → the executable
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog S.input) k cs' = o) →
      o ≠ .outOfFuel → Clif.DepthLe B.env (prog S.input) d cs' →
      (∀ F, Clif.runLoop B.env (prog S.input) (F + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs') →
      ExecRefines (art S.input f').fb (art S.input f').base
        (xreg 30 r) (step S.input B file) r (RelocAt S.input) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      have := compileExe_correct_peak h B hB hH hf' F d hX ho hr hdT
        (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, ⟨m, hm⟩, hdT⟩ := hret vals cm hrun
    rw [hpe'] at hm hdT
    exact ⟨rv', hrel, hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F hF =>
      trapsExplicit_of_runD hL hfP' hcs' ho.symbols hdT hF⟩
  · obtain ⟨⟨m, hm⟩, hdT⟩ := htrap hnmt c hrun
    rw [hpe'] at hm hdT
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F _ => htr F

end Link
