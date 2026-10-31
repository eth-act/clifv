import FV.Front.Exe
import FV.Front.RawProof
import FV.Link.DeadCleanupExeTrapTNB

/-!
# The frontend bundle theorems with callee traps (`try_call` callees included) without the
# memory-bound premise (A2/B1)

`bundle_correct_source_trapT{,_peak}` and `bundle_correct_raw_trapT{,_peak}` (`compileExeU`, S9e)
without the premise that the source run's memories lie below `2^64`
(`∀ s', SReach E _ cs s' → MemBounded s'.mem`): composed from
`Link.DeadCleanup.compileExe_correct_source_trapT{,_peak}_nobnd`, which derive it.
-/

namespace Front

open Clif E2E.LinkCheck Link
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Opt.Legalize128

/-- `bundle_correct_source_trapT` without the premise that the source run's memories lie below `2^64`
(A2/B1).
**The shipped executable compiler refines the frontend bundle's program, callee traps
included** (`bundle_correct_source` with `Link.DeadCleanup.compileExe_correct_source_trapT`): a
return as there; a trap of the units' program's run (without load/store traps; the target runs
under the run premise `TrapsDT` at every fuel) is an executable state at a trap with the same code
(`ExecRefinesC`). -/
theorem bundle_correct_source_trapT_nobnd {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup
      S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
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
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ K, (sys S.inputCleanup B).std.TrapsDT K (legalize (f.rename σ.fwd)) cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source_trapT_nobnd (cs := cs.ren σ) h hsrc B hB hH hBT
    hlegal hsig hf' hc hX ho hr (clifEntry_ren hcs) (by simpa using hexp)
    (by simpa using hsl) hmem M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- `bundle_correct_source_trapT_peak` without the premise that the source run's memories lie below `2^64`
(A2/B1).
**`bundle_correct_source_trapT`, recursive programs included** (with
`Link.DeadCleanup.compileExe_correct_source_trapT_peak`): the stack `frameDrop + (D * d + pbMax)`
(#581: the deepest activation's stack probes write up to `pbMax` bytes below its frame) from the units' run's call
depth `d`; the target runs under `TrapsDT` of `LinkSys.peak` at every fuel. -/
theorem bundle_correct_source_trapT_peak_nobnd {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r
      args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hd : Clif.DepthLe E (link us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, ((sys S.inputCleanup B).peak F).TrapsDT d (legalize (f.rename σ.fwd)) cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source_trapT_peak_nobnd (cs := cs.ren σ) h hsrc B hB hH
    hBT hlegal hsig hf' d hX ho hr (clifEntry_ren hcs) (by simpa using hexp)
    (by simpa using hsl) hmem
    (by rw [hP, hE]; exact depthLe_ren hd) M
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- `bundle_correct_raw_trap` without the premise that the source run's memories lie below `2^64`
(A2/B1).
**The shipped executable compiler refines cg_clif's program, callee traps included**: as
`bundle_correct_source_trapT`, about the runs of cg_clif's program `rawLink us sc` under a naming
`sc` of its module identities that respects its declarations (`RawScopingOk`). -/
theorem bundle_correct_raw_trapT_nobnd {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup
      S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
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
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ K, (sys S.inputCleanup B).std.TrapsDT K (legalize (f.rename σ.fwd)) cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf ⊢
  exact bundle_correct_source_trapT_nobnd hb h hsrc hus hσ E B hE hB hH hBT hlegal hsig hf hc hX
    ho hr hcs hexp hsl hmem M

/-- `bundle_correct_raw_trap_peak` without the premise that the source run's memories lie below `2^64`
(A2/B1).
**The shipped executable compiler refines cg_clif's program, callee traps and recursive
programs included**: as `bundle_correct_source_trapT_peak`, about the runs of cg_clif's program
`rawLink us sc` (`RawScopingOk`). -/
theorem bundle_correct_raw_trapT_peak_nobnd {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.inputCleanup B)) (hH : HooksSim S.inputCleanup B)
    (hBT : (sys S.inputCleanup B).BaseTrapsOk)
    (hlegal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r
      args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hd : Clif.DepthLe E (rawLink us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, ((sys S.inputCleanup B).peak F).TrapsDT d (legalize (f.rename σ.fwd)) cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hd ⊢
  exact bundle_correct_source_trapT_peak_nobnd hb h hsrc hus hσ E B hE hB hH hBT hlegal hsig hf d
    hX ho hr hcs hexp hsl hmem hd M

end Front
