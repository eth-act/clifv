import FV.Front.RawExe
import FV.Link.DeadCleanupExeSourceT

/-!
# The executable compiler with the typed scope refines cg_clif's program (S11e6, #419)

`FV/Front/Exe.lean` and `FV/Front/RawExe.lean` for `Link.DeadCleanup.compileExeT`, the compiler
`lean-link --verified` runs on a typed input (`compileExe` on `InScopeP`, otherwise the typed
input conditions `InScopePT`, the Lean linker and the output checks `OutOkTCleanup`): the typed
source theorems `Link.DeadCleanup.compileExeT_correct_source{,_peak}` composed with the renaming
of the units' program (`buildSpec_srcProg`, `Clif.runLoop_ren`) and with the raw dumps' program
(`rawLink_eq_link`), exactly as the integer theorems. The returned values are placed by class
(`ExecRefinesT`).

* `bundle_correct_sourceT`, `bundle_correct_source_peakT`: about the units' program under a
  scoping `sc`;
* `bundle_correct_rawT`, `bundle_correct_raw_peakT`: about cg_clif's program as its dumps wrote
  it (`rawLink us sc`).
-/

namespace Front

open Clif E2E.LinkCheck Link

section Cleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Opt.Legalize128

/-- **The executable compiler with the typed scope refines the frontend bundle's program**
(`bundle_correct_source` for `Link.DeadCleanup.compileExeT`): for the `LinkSpec` `lean-link`
builds from the bundle and `compileExeT S file0 = .ok file`, about the runs of the units' program
under a scoping `sc` in the environment `E` (the executable's `B.env = E.ren σ`): a return of the
source run from `f`'s entry `cs` is the executable's return of the split results, each in the ABI
return register of its class, the memory renamed to the linked names; a trap (of a source run
without load/store traps) is the same trap. -/
theorem bundle_correct_sourceT {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeT S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExeT_correct_source (cs := cs.ren σ) h hsrc B hB hH hlegal hsig hf' hc hX ho hr
    (clifEntry_ren hcs) (by simpa using hexp) (by simpa using hsl) hmem
    (by rw [hP, hE]; exact bnd_ren hbnd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **The executable compiler with the typed scope refines cg_clif's program**
(`bundle_correct_raw` for `Link.DeadCleanup.compileExeT`): as `bundle_correct_sourceT`, about the
runs of cg_clif's program `rawLink us sc` under a naming `sc` of its module identities that
respects its declarations (`RawScopingOk`). -/
theorem bundle_correct_rawT {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeT S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd ⊢
  exact bundle_correct_sourceT hb h hsrc hus hσ E B hE hB hH hlegal hsig hf hc hX ho hr hcs hexp hsl hmem hbnd M

/-- **The executable compiler with the typed scope refines the frontend bundle's program,
recursive programs included** (`bundle_correct_source_peak` for `Link.DeadCleanup.compileExeT`):
`Link.DeadCleanup.compileExeT_correct_source_peak` composed as in `bundle_correct_sourceT`; the
stack `frameDrop + (D * d + pbMax)` (#581: the deepest activation's stack probes write up to
`pbMax` bytes below its frame) from the source run's call depth `d` (`Clif.DepthLe` of the units' program). -/
theorem bundle_correct_source_peakT {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeT S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (link us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExeT_correct_source_peak (cs := cs.ren σ) h hsrc B hB hH hlegal hsig hf' d hX ho hr
    (clifEntry_ren hcs) (by simpa using hexp) (by simpa using hsl) hmem
    (by rw [hP, hE]; exact bnd_ren hbnd) (by rw [hP, hE]; exact depthLe_ren hd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **The executable compiler with the typed scope refines cg_clif's program, recursive programs
included** (`bundle_correct_raw_peak` for `Link.DeadCleanup.compileExeT`): as
`bundle_correct_source_peakT`, about the runs of cg_clif's program `rawLink us sc` under a naming
`sc` of its module identities that respects its declarations (`RawScopingOk`). -/
theorem bundle_correct_raw_peakT {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeT S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (rawLink us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefinesT (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesT (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd hd ⊢
  exact bundle_correct_source_peakT hb h hsrc hus hσ E B hE hB hH hlegal hsig hf d hX ho hr hcs hexp hsl hmem hbnd hd M

end Cleanup

end Front
