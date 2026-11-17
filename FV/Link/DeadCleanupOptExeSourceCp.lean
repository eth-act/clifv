import FV.Link.DeadCleanupOptExe
import FV.Link.CpSource

/-! # The optimising cleanup compiler refines the bundle's program (#1052)

`Link.DeadCleanup.compileExeOpt_correct_source{,_peak}` (`FV/Link/DeadCleanupOptExe.lean`) about
the **bundle's program**: through the `i128` legalisation and constant-phi removal (`cpSource`,
`cpSource_depth`, `FV/Link/CpSource.lean`) to the input's program, then
`compileExeOpt_correct{,_peak}` (the mid-end and the executable).
`Link.ReturnPinCompilerWith.attempt_correct_source{,_peak}Cp` (`FV/Link/ReturnPinExeSourceCp.lean`)
says why.
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128

/-- **The optimising executable compiler refines the bundle's program** (#1052):
`compileExeOpt_correct_source` about the program `I0.srcProg` of an input in the source domain
whose constant-phi removal is the input's functions (`hcp`; in `lean-link`, `I0 = S0.input0` and
`S` the placement of `S0.cp`): through the `i128` legalisation and constant-phi removal
(`cpSource`) to the run of the input's program from the entry of its function `fC` named `f`'s
name, then the mid-end and the executable (`compileExeOpt_correct`). For
`compileExeOpt S file0 = .ok file` and an outside call of the compiled code of the optimised
function `f'` named `f`'s name (no call cycle reachable from it) with the ABI-split arguments
`args'` of `args`: a return of `I0`'s source run from `f`'s entry `cs` is the executable's return
of the results split by `f`'s return groups with the same memory; a trap (of a source run without
load/store traps, the optimised runs' traps explicit) is the same trap. -/
theorem compileExeOpt_correct_sourceCp {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B)) (hH : HooksSim S.opt.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.opt.inputCleanup S.opt.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (DeadCleanupStackBound.stackFn S.opt.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
          (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.returned vals' cm)) ∧
    ((∀ K, TrapsExplicit (Clif.linkEnvN (prog S.opt.inputCleanup) B.env K) (prog S.opt.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hR := optRel_prog S
  have hpeI : S.inputCleanup.prog = prog S.inputCleanup := (prog_eq S).symm
  have hcpI : S.inputCleanup.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program, from the optimised input's linked system
  have hC : ProgCtx I0.srcProg B.env (fun n => S.inputCleanup.syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpeI]; exact hR.nodup hL.names) (by rw [hpeI]; exact hR.free hL.free)
      (by rw [hpeI]; exact hR.declSig hL.declSig) (by rw [hpeI]; exact hR.indScope hL.indScope)
      hlegal (by rw [hpeI]; exact hsig)
  -- the input's (constant-phi-removed) function `fC` named `n`, and its entry `csC`
  have hfL : I0.prog.func? n = some (legalize f) := by
    rw [LinkInput.prog_eq]; exact hC.func?_some hf
  obtain ⟨fC, hfC, -⟩ := ((LinkInput.cpRel hcpI).func? n).1 _ hfL
  have hfC' : (prog S.inputCleanup).func? n = some fC := by rw [← hpeI]; exact hfC
  have hcs' := hr.entry
  obtain ⟨csC, hcsC, hrC, hsC, hmC, -, -⟩ := hR.entry hfC' hf' hcs'
  -- the bundle's run → the input's run → the optimised program and the executable
  obtain ⟨hret, htrap⟩ := cpSource hcpI hC hkeep hf hfC hcs hcsC hexp (hsC.trans hsl)
    (hmC.trans hmem) (fun _ => by rw [← hmem]; exact ho.symbols) hbnd M
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, m, hm⟩ := hret vals cm hrun
    rw [hpeI] at hm
    exact ⟨rv', hrel, (compileExeOpt_correct h B hB hH hkeep hfC' hf' hc hX ho hr hcsC hrC hsC hmC
      m).1 _ _ hm⟩
  · obtain ⟨m, hm⟩ := htrap hnmt c hrun
    rw [hpeI] at hm
    exact (compileExeOpt_correct h B hB hH hkeep hfC' hf' hc hX ho hr hcsC hrC hsC hmC m).2 htr c hm

/-- **The optimising executable compiler refines the bundle's program, recursive programs
included** (#1052): `compileExeOpt_correct_source_peak` about the program `I0.srcProg` of an input
in the source domain whose constant-phi removal is the input's functions; no call-graph premise;
the outside caller provides `frameDrop + (D * d + pbMax)` bytes of stack, where `d` bounds the
call depth of `I0`'s source run (`Clif.DepthLe`): the legalisation, constant-phi removal and the
mid-end keep the call depth of the runs they refine. -/
theorem compileExeOpt_correct_source_peakCp {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeOpt S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys S.opt.inputCleanup B)) (hH : HooksSim S.opt.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog S.opt.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.opt.inputCleanup (BinCheck.roByte S.opt.inputCleanup S.opt.data) f'
      (frameDrop (art S.opt.inputCleanup f').af + (S.opt.inputCleanup.D * d + pbMax S.opt.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.opt.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs) (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
          (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.opt.inputCleanup) B.env F d) (prog S.opt.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefines (art S.opt.inputCleanup f').fb (art S.opt.inputCleanup f').base (xreg 30 r)
        (step S.opt.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.opt.inputCleanup) (.trapped c)) := by
  have hL := linkOk_opt h B hB
  have hR := optRel_prog S
  have hpeI : S.inputCleanup.prog = prog S.inputCleanup := (prog_eq S).symm
  have hcpI : S.inputCleanup.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program, from the optimised input's linked system
  have hC : ProgCtx I0.srcProg B.env (fun n => S.inputCleanup.syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpeI]; exact hR.nodup hL.names) (by rw [hpeI]; exact hR.free hL.free)
      (by rw [hpeI]; exact hR.declSig hL.declSig) (by rw [hpeI]; exact hR.indScope hL.indScope)
      hlegal (by rw [hpeI]; exact hsig)
  -- the input's (constant-phi-removed) function `fC` named `n`, and its entry `csC`
  have hfL : I0.prog.func? n = some (legalize f) := by
    rw [LinkInput.prog_eq]; exact hC.func?_some hf
  obtain ⟨fC, hfC, -⟩ := ((LinkInput.cpRel hcpI).func? n).1 _ hfL
  have hfC' : (prog S.inputCleanup).func? n = some fC := by rw [← hpeI]; exact hfC
  have hcs' := hr.entry
  obtain ⟨csC, hcsC, hrC, hsC, hmC, -, -⟩ := hR.entry hfC' hf' hcs'
  -- the bundle's run → the input's run → the optimised program and the executable
  obtain ⟨hret, htrap⟩ := cpSource_depth hcpI hC hkeep hf hfC hcs hcsC hexp (hsC.trans hsl)
    (hmC.trans hmem) (fun _ => by rw [← hmem]; exact ho.symbols) hbnd hd M
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, ⟨m, hm⟩, hdC⟩ := hret vals cm hrun
    rw [hpeI] at hm hdC
    exact ⟨rv', hrel, (compileExeOpt_correct_peak h B hB hH hkeep hfC' hf' d hX ho hr hcsC hrC hsC
      hmC hdC m).1 _ _ hm⟩
  · obtain ⟨⟨m, hm⟩, hdC⟩ := htrap hnmt c hrun
    rw [hpeI] at hm hdC
    exact (compileExeOpt_correct_peak h B hB hH hkeep hfC' hf' d hX ho hr hcsC hrC hsC hmC hdC
      m).2 htr c hm

end Link.DeadCleanup
