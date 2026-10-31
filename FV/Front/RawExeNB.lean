import FV.Front.RawExe
import FV.Link.DeadCleanupExeSourceNB

/-!
# The frontend bundle theorems without the memory-bound premise (A2/B1)

`bundle_correct_source{,_peak}` and `bundle_correct_raw{,_peak}` (the shipped compiler) without
the premise that the source run's memories lie below `2^64`
(`∀ s', SReach E _ cs s' → MemBounded s'.mem`): composed from
`Link.DeadCleanup.compileExe_correct_source{,_peak}_nobnd`, which derive it.
-/

namespace Front

open Clif E2E.LinkCheck Link
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Opt.Legalize128

/-- `bundle_correct_source` without the premise that the source run's memories lie below `2^64` (A2/B1).
**The shipped executable compiler refines the frontend bundle's program** (T7e):
`Link.DeadCleanup.compileExe_correct_source` for the `LinkSpec` `lean-link` builds from the
bundle (`buildSpec b = .ok S`), about the runs of the units' program under a scoping `sc`
(`link us sc`, alpha-equivalent to the linked one by `σ`: `link_alpha`) in the environment `E`
(the executable's `B.env = E.ren σ`): a return of the source run from `f`'s entry `cs` is the
executable's return of the split results, the memory renamed to the linked names; a trap (of a
source run without load/store traps) is the same trap. -/
theorem bundle_correct_source_nobnd {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
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
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source_nobnd (cs := cs.ren σ) h hsrc B hB hH hlegal hsig hf' hc hX ho hr
    (clifEntry_ren hcs) (by simpa using hexp) (by simpa using hsl) hmem M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- `bundle_correct_source_peak` without the premise that the source run's memories lie below `2^64` (A2/B1).
**The shipped executable compiler refines the frontend bundle's program, recursive
programs included** (T7e): `Link.DeadCleanup.compileExe_correct_source_peak` composed as in
`bundle_correct_source`; the stack `frameDrop + (D * d + pbMax)` (#581: the deepest activation's
stack probes write up to `pbMax` bytes below its frame) from the source run's call depth `d` (`Clif.DepthLe` of the
units' program). -/
theorem bundle_correct_source_peak_nobnd {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
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
    (hd : Clif.DepthLe E (link us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source_peak_nobnd (cs := cs.ren σ) h hsrc B hB hH hlegal hsig hf' d hX ho hr
    (clifEntry_ren hcs) (by simpa using hexp) (by simpa using hsl) hmem
    (by rw [hP, hE]; exact depthLe_ren hd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- `bundle_correct_raw` without the premise that the source run's memories lie below `2^64` (A2/B1).
**The shipped executable compiler (`bundle_correct_source`), entries without a reachable call cycle refines cg_clif's program**: as `bundle_correct_source`, about the runs of cg_clif's
program `rawLink us sc` under a naming `sc` of its module identities that respects its declarations
(`RawScopingOk`). -/
theorem bundle_correct_raw_nobnd {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
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
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf ⊢
  exact bundle_correct_source_nobnd hb h hsrc hus hσ E B hE hB hH hlegal hsig hf hc hX ho hr hcs hexp hsl hmem M

/-- `bundle_correct_raw_peak` without the premise that the source run's memories lie below `2^64` (A2/B1).
**The shipped executable compiler, recursive programs included (`bundle_correct_source_peak`) refines cg_clif's program**: as `bundle_correct_source_peak`, about the runs of cg_clif's
program `rawLink us sc` under a naming `sc` of its module identities that respects its declarations
(`RawScopingOk`). -/
theorem bundle_correct_raw_peak_nobnd {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
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
    (hd : Clif.DepthLe E (rawLink us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hd ⊢
  exact bundle_correct_source_peak_nobnd hb h hsrc hus hσ E B hE hB hH hlegal hsig hf d hX ho hr hcs hexp hsl hmem hd M

end Front
