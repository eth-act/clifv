import FV.Link.DeadCleanupExeSourceT
import FV.Link.CpSource

/-! # The shipped executable compiler on the typed scope refines the bundle's program (#1052)

`compileExe_correct_source{,_peak}_okT` and `compileExeT_correct_source{,_peak}`
(`FV/Link/DeadCleanupExeSourceT.lean`, returned values by class, `ExecRefinesT`) about the
**bundle's program** through the `i128` legalisation and constant-phi removal, as
`Link.ReturnPinCompilerWith.attempt_correct_source{,_peak}Cp` (`FV/Link/ReturnPinExeSourceCp.lean`,
which says why): for an input `I0` in `SrcScopeB` whose constant-phi removal is `S`'s functions
(`hcp`), the compiled function `f'` named `f`'s name (`cpSource`, `cpSource_depth`).
-/

namespace Link.DeadCleanup
set_option autoImplicit false
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend LinkSpec Opt.Legalize128

/-- **The shipped executable compiler on the typed scope refines the bundle's program** (#1052):
`compileExe_correct_source_okT` about the program `I0.srcProg` of an input in the source domain whose constant-phi removal is the compiled input's functions (`hcp`; in `lean-link`, `I0 = S0.input0` and `S` the
placement of `S0.cp`). For `leanLink S file0 = .ok file` on a typed in-scope input passing the output checks (`okBCleanupT`), a source function `f` of `I0`,
and an outside call of the code of the compiled function `f'` named `f`'s name (no call cycle
reachable from it) with the ABI-split arguments `args'` of `args`: a return of `I0`'s source run
from `f`'s entry `cs` is the executable's return of the results split by `f`'s return groups with
the same memory, each in the ABI return register of its class (`ExecRefinesT`); a trap (of a source run without load/store traps, the target runs' traps
explicit) is the same trap. -/
theorem compileExe_correct_source_okTCp {S : LinkSpec} {file0 file : ByteArray}
    (hok : okBCleanupT S.inputCleanup = true) (h : leanLink S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog S.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (DeadCleanupStackBound.stackFn S.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).OkT :=
    okBCleanup_soundT hok (baseOk_F hB) fun _ _ => trivial
  have hpe' : S.inputCleanup.prog = prog S.inputCleanup := (prog_eq S).symm
  have hcpI : S.inputCleanup.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program
  have hC : ProgCtx I0.srcProg B.env (fun n => S.inputCleanup.syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hcs' := hr.entry
  have hfI : S.inputCleanup.prog.func? n = some f' := by rw [hpe']; exact hf'
  have hfP' : f' ∈ (prog S.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  -- the bundle's run → the compiled program's run
  obtain ⟨hret, htrap⟩ := cpSource hcpI hC hkeep hf hfI hcs hcs' hexp hsl hmem
    (fun _ => by rw [← hmem]; exact ho.symbols) hbnd M
  -- the compiled program's run → the executable
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog S.inputCleanup) k cs' = o) →
      o ≠ .outOfFuel →
      (∀ K, Clif.runLoop B.env (prog S.inputCleanup) (K + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs') →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) o := by
    rintro o ⟨k, hk⟩ hof htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ K =>
      have := binary_correct_exec_provenT hok (codeMap_leanLink h) (binOk_leanLink h)
        (gotOk_leanLink h) B hB hH hf' hc K hX ho (outsideAvoids_leanLink h _ _ _ _ _) hr
        (htr K hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, m, hm⟩ := hret vals cm hrun
    rw [hpe'] at hm
    exact ⟨rv', hrel, hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K hK =>
      trapsExplicit_of_runT hL hfP' hcs' ho.symbols hK⟩
  · obtain ⟨m, hm⟩ := htrap hnmt c hrun
    rw [hpe'] at hm
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) fun K _ => htr K

/-- **The shipped executable compiler on the typed scope refines the bundle's program, recursive programs included** (#1052):
`compileExe_correct_source_okT_peak` about the program `I0.srcProg` of an input in the source domain whose constant-phi removal is the compiled input's functions; no
call-graph premise; the outside caller of `f'`'s code provides `frameDrop + (D * d + pbMax)` bytes
of stack, where `d` bounds the call depth of `I0`'s source run from `cs` (`Clif.DepthLe`). A
return of the source run is the executable's return of the results split by `f`'s return groups
with the same memory, each in the ABI return register of its class (`ExecRefinesT`); a trap (of a source run without load/store traps, the target runs'
traps explicit under `Clif.linkEnvD` at every fuel) is the same trap. -/
theorem compileExe_correct_source_peak_okTCp {S : LinkSpec} {file0 file : ByteArray}
    (hok : okBCleanupT S.inputCleanup = true) (h : leanLink S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog S.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (frameDrop (art S.inputCleanup f').af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hL : (LinkSys.ofInputCleanup S.inputCleanup B fun _ => True).OkT :=
    okBCleanup_soundT hok (baseOk_F hB) fun _ _ => trivial
  have hpe' : S.inputCleanup.prog = prog S.inputCleanup := (prog_eq S).symm
  have hcpI : S.inputCleanup.funcs = I0.funcs.map FnInput.cp := hcp
  -- the source domain of the bundle's program
  have hC : ProgCtx I0.srcProg B.env (fun n => S.inputCleanup.syms.lookup n) :=
    srcCtx_cp hcpI hsrc (by rw [hpe']; exact hL.names) (by rw [hpe']; exact hL.free)
      (by rw [hpe']; exact hL.declSig) (by rw [hpe']; exact hL.indScope) hlegal
      (by rw [hpe']; exact hsig)
  have hcs' := hr.entry
  have hfI : S.inputCleanup.prog.func? n = some f' := by rw [hpe']; exact hf'
  have hfP' : f' ∈ (prog S.inputCleanup).funcs := (Clif.Program.func?_some hf').1
  -- the bundle's run (call depth `d`) → the compiled program's run (call depth `d`)
  obtain ⟨hret, htrap⟩ := cpSource_depth hcpI hC hkeep hf hfI hcs hcs' hexp hsl hmem
    (fun _ => by rw [← hmem]; exact ho.symbols) hbnd hd M
  -- the compiled program's run of call depth at most `d` → the executable
  have hexe : ∀ o, (∃ k, Clif.runLoop B.env (prog S.inputCleanup) k cs' = o) →
      o ≠ .outOfFuel → Clif.DepthLe B.env (prog S.inputCleanup) d cs' →
      (∀ F, Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs' = o →
        TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) o := by
    rintro o ⟨k, hk⟩ hof hdT htr
    cases k with
    | zero => exact absurd hk.symm (by simpa using hof)
    | succ F =>
      have := binary_correct_exec_peak_provenT hok (codeMap_leanLink h) (binOk_leanLink h)
        (gotOk_leanLink h) B hB hH hf' F d hX ho (outsideAvoids_leanLink h _ _ _ _ _) hr hdT
        (htr F hk)
      rw [hk] at this
      exact this
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · obtain ⟨rv', hrel, ⟨m, hm⟩, hdT⟩ := hret vals cm hrun
    rw [hpe'] at hm hdT
    exact ⟨rv', hrel, hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F hF =>
      trapsExplicit_of_runDT hL hfP' hcs' ho.symbols hdT hF⟩
  · obtain ⟨⟨m, hm⟩, hdT⟩ := htrap hnmt c hrun
    rw [hpe'] at hm hdT
    exact hexe _ ⟨m, hm⟩ (fun h => by cases h) hdT fun F _ => htr F

/-- **`compileExeT` refines the bundle's program** (#1052):
`compileExeT_correct_source` about the program `I0.srcProg` of an input in the source domain whose constant-phi removal is the compiled input's functions (`hcp`; in `lean-link`, `I0 = S0.input0` and `S` the
placement of `S0.cp`). For `compileExeT S file0 = .ok file` (`compileExe` on `InScopeP`, the typed branch otherwise), a source function `f` of `I0`,
and an outside call of the code of the compiled function `f'` named `f`'s name (no call cycle
reachable from it) with the ABI-split arguments `args'` of `args`: a return of `I0`'s source run
from `f`'s entry `cs` is the executable's return of the results split by `f`'s return groups with
the same memory, each in the ABI return register of its class (`ExecRefinesT`); a trap (of a source run without load/store traps, the target runs' traps
explicit) is the same trap. -/
theorem compileExeT_correct_sourceCp {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog S.inputCleanup).func? n = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (DeadCleanupStackBound.stackFn S.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hok : okBCleanupT S.inputCleanup = true ∧ leanLink S file0 = .ok file := by
    rcases compileExeT_spec h with hc0 | ⟨hin, hout, hl⟩ | ⟨hI, hl⟩
    · obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe hc0
      exact ⟨okBT_leanLink hin hout hl, hl⟩
    · exact ⟨okBT_leanLink hin hout hl, hl⟩
    · exact ⟨hI, hl⟩
  exact compileExe_correct_source_okTCp hok.1 hok.2 hcp hsrc B hB hH hkeep hlegal hsig hf hf' hc hX
    ho hr hcs hexp hsl hmem hbnd M

/-- **`compileExeT` refines the bundle's program, recursive programs included** (#1052):
`compileExeT_correct_source_peak` about the program `I0.srcProg` of an input in the source domain whose constant-phi removal is the compiled input's functions; no
call-graph premise; the outside caller of `f'`'s code provides `frameDrop + (D * d + pbMax)` bytes
of stack, where `d` bounds the call depth of `I0`'s source run from `cs` (`Clif.DepthLe`). A
return of the source run is the executable's return of the results split by `f`'s return groups
with the same memory, each in the ABI return register of its class (`ExecRefinesT`); a trap (of a source run without load/store traps, the target runs'
traps explicit under `Clif.linkEnvD` at every fuel) is the same trap. -/
theorem compileExeT_correct_source_peakCp {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeT S file0 = .ok file) {I0 : LinkInput}
    (hcp : S.funcs = I0.funcs.map FnInput.cp) (hsrc : SrcScopeB I0 = true)
    (B : BaseEnv) (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ I0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : I0.srcProg.func? n = some f)
    (hf' : (prog S.inputCleanup).func? n = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (frameDrop (art S.inputCleanup f').af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env I0.srcProg cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env I0.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env I0.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env I0.srcProg cs → ∀ c,
      Clif.runLoop B.env I0.srcProg M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hok : okBCleanupT S.inputCleanup = true ∧ leanLink S file0 = .ok file := by
    rcases compileExeT_spec h with hc0 | ⟨hin, hout, hl⟩ | ⟨hI, hl⟩
    · obtain ⟨hin, hout, hl⟩ := typedPremises_of_compileExe hc0
      exact ⟨okBT_leanLink hin hout hl, hl⟩
    · exact ⟨okBT_leanLink hin hout hl, hl⟩
    · exact ⟨hI, hl⟩
  exact compileExe_correct_source_peak_okTCp hok.1 hok.2 hcp hsrc B hB hH hkeep hlegal hsig hf hf' d
    hX ho hr hcs hexp hsl hmem hbnd hd M

end Link.DeadCleanup
