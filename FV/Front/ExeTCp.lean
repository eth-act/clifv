import FV.Front.ExeT
import FV.Link.DeadCleanupExeSourceTCp
import FV.Link.TypedStockShared

/-!
# The typed executable compiler refines cg_clif's program through constant-phi removal (#1088)

`Front.bundle_correct_{source,raw}{,_peak}T` (`FV/Front/ExeT.lean`) are about
`compileExeT S file0 = .ok file` for the bundle's own spec `S` (`buildSpec b = .ok S`). `lean-link`
compiles the Lean compiler's placement of the constant-phi-removed spec `S0.cp`, which is
`buildSpec` of no bundle when constant-phi removal changes a function. The theorems here take the
compiled spec `S` and the bundle's spec `S0` apart: `buildSpec b = .ok S0`,
`S.funcs = S0.input0.funcs.map FnInput.cp` (`hcp`; in `lean-link` `S0` is `buildSpec` of the bundle
read and `S` its placement of `S0.cp`, by `rfl`), `SrcScopeB S0.input0` (decided by `lean-link`),
and compose `Link.DeadCleanup.compileExeT_correct_source{,_peak}Cp` (#1052: the legalisation's and
constant-phi removal's refinements, `Link.cpSource`) with the renaming of the units' program
(`buildSpec_srcProg`, `Clif.runLoop_ren`) and the raw dumps' program (`rawLink_eq_link`), as
`ExeT.lean` does. The compiled function `f'` is explicit (`hf'`), as in the `Cp` theorems.

* `bundle_correct_sourceTCp`, `bundle_correct_source_peakTCp`: the units' program under a scoping;
* `bundle_correct_rawTCp`, `bundle_correct_raw_peakTCp`: cg_clif's program as its dumps wrote it.
-/

namespace Front

open Clif E2E.LinkCheck Link

/-- **`lean-link`'s `hcp` on the typed route**: the spec it compiles there, the cleanup layout of
the constant-phi-removed spec (`TypedStockShared.placedFrom S0.cp A`, any results `A`), has
`S0`'s constant-phi removals as its functions. -/
theorem placedFrom_cp_funcs (S0 : LinkSpec) (A : List (Except String E2E.Art)) :
    (TypedStockShared.placedFrom S0.cp A).funcs = S0.input0.funcs.map FnInput.cp := rfl

section Cleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Opt.Legalize128

/-- **`compileExeT` of the constant-phi-removed spec refines the frontend bundle's program**
(`bundle_correct_sourceT` through constant-phi removal): for the bundle's spec `S0`
(`buildSpec b = .ok S0`) in the source domain, a compiled spec `S` whose functions are `S0`'s
constant-phi removals and `compileExeT S file0 = .ok file`, about the runs of the units' program
under a scoping `sc` in the environment `E` (the executable's `B.env = E.ren σ`): a return of the
source run from `f`'s entry `cs` is the executable's return (from the compiled function `f'` named
`f`'s linked name) of the split results, each in the ABI return register of its class, the memory
renamed to the linked names; a trap (of a source run without load/store traps) is the same trap. -/
theorem bundle_correct_sourceTCp {b : Bundle} {S0 S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S0) (hcp : S.funcs = S0.input0.funcs.map FnInput.cp)
    (h : Link.DeadCleanup.compileExeT S file0 = .ok file)
    (hsrc : SrcScopeB S0.input0 = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S0.input0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : (link us sc).func? n = some f)
    (hf' : (prog S.inputCleanup).func? (σ.fwd n) = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (DeadCleanupStackBound.stackFn S.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S0.input0.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]
  have hf'' : S0.input0.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExeT_correct_sourceCp (cs := cs.ren σ) h hcp hsrc B hB hH hkeep
    hlegal hsig hf'' hf' hc hX ho hr (clifEntry_ren hcs) (by simpa using hexp) (by simpa using hsl)
    hmem (by rw [hP, hE]; exact bnd_ren hbnd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **`compileExeT` of the constant-phi-removed spec refines cg_clif's program** (`bundle_correct_rawT`
through constant-phi removal): as `bundle_correct_sourceTCp`, about the runs of cg_clif's program
`rawLink us sc` under a naming `sc` of its module identities that respects its declarations
(`RawScopingOk`). -/
theorem bundle_correct_rawTCp {b : Bundle} {S0 S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S0) (hcp : S.funcs = S0.input0.funcs.map FnInput.cp)
    (h : Link.DeadCleanup.compileExeT S file0 = .ok file)
    (hsrc : SrcScopeB S0.input0 = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S0.input0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (hf' : (prog S.inputCleanup).func? (σ.fwd n) = some f')
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f')
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (DeadCleanupStackBound.stackFn S.inputCleanup f') r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd ⊢
  exact bundle_correct_sourceTCp hb hcp h hsrc hus hσ E B hE hB hH hkeep hlegal hsig hf hf' hc hX ho
    hr hcs hexp hsl hmem hbnd M

/-- **`compileExeT` of the constant-phi-removed spec refines the frontend bundle's program,
recursive programs included** (`bundle_correct_source_peakT` through constant-phi removal):
`Link.DeadCleanup.compileExeT_correct_source_peakCp` composed as in `bundle_correct_sourceTCp`;
the stack `frameDrop + (D * d + pbMax)` from the source run's call depth `d` (`Clif.DepthLe` of
the units' program). -/
theorem bundle_correct_source_peakTCp {b : Bundle} {S0 S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S0) (hcp : S.funcs = S0.input0.funcs.map FnInput.cp)
    (h : Link.DeadCleanup.compileExeT S file0 = .ok file)
    (hsrc : SrcScopeB S0.input0 = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S0.input0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : (link us sc).func? n = some f)
    (hf' : (prog S.inputCleanup).func? (σ.fwd n) = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (frameDrop (art S.inputCleanup f').af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (link us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S0.input0.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]
  have hf'' : S0.input0.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExeT_correct_source_peakCp (cs := cs.ren σ) h hcp hsrc B hB hH
    hkeep hlegal hsig hf'' hf' d hX ho hr (clifEntry_ren hcs) (by simpa using hexp)
    (by simpa using hsl) hmem (by rw [hP, hE]; exact bnd_ren hbnd)
    (by rw [hP, hE]; exact depthLe_ren hd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **`compileExeT` of the constant-phi-removed spec refines cg_clif's program, recursive programs
included** (`bundle_correct_raw_peakT` through constant-phi removal): as
`bundle_correct_source_peakTCp`, about cg_clif's program `rawLink us sc` (`RawScopingOk`). -/
theorem bundle_correct_raw_peakTCp {b : Bundle} {S0 S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S0) (hcp : S.funcs = S0.input0.funcs.map FnInput.cp)
    (h : Link.DeadCleanup.compileExeT S file0 = .ok file)
    (hsrc : SrcScopeB S0.input0 = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hkeep : Opt.EnvKeepsSymbols B.env)
    (hlegal : (∃ f ∈ S0.input0.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f f' : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (hf' : (prog S.inputCleanup).func? (σ.fwd n) = some f') (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) f'
      (frameDrop (art S.inputCleanup f').af + (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B f' r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (rawLink us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup f').fb (art S.inputCleanup f').base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd hd ⊢
  exact bundle_correct_source_peakTCp hb hcp h hsrc hus hσ E B hE hB hH hkeep hlegal hsig hf hf' d
    hX ho hr hcs hexp hsl hmem hbnd hd M

end Cleanup

end Front
