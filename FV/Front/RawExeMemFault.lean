import FV.Front.Exe
import FV.Front.RawProof
import FV.Link.DeadCleanupExeMemFault

/-!
# The shipped executable compiler refines cg_clif's program, memory faults included (A3, #412, slice F8d)

`docs/plans/memfault.md`. `FV/Front/RawExeMemTrap.lean`'s trap halves say, for the executable's
run under the fault-aware machine `stepF mp`, only that **if** it reaches the trapping atomic
(`atomic_rmw`, `atomic_cas`: their CLIF trap is an access outside every live allocation,
Cranelift's `heap_oob`), its `ldaxr` faults under the map; they do not say that no earlier step
of the run faults under `mp`. Here the trap halves of the same refinements with the additional
premise `MapRelRW mp` (F8): every byte the map does not allow to be written lies outside the
reserved stack `N`, the stack arguments and every allocation of the entry's CLIF memory, and the
program's code is readable — so every byte valid in the entry's CLIF memory is mapped read-write
(read-only data included; F8a, #472, will relax it), and no earlier step of the run faults under
`mp`: the observable is `ExecTrapF` (`E2E.DeadCleanupExecBytes.ExecTrapF`), a trap site of the
entry function with the code whose instruction errs (`udf`) or faults under `mp`, with no
faulting step before it and its step there errs.

* `bundle_correct_source_memtrapF_rw{,_peak}`: the units' program under a scoping `sc`;
* `bundle_correct_raw_memtrapF_rw{,_peak}`: cg_clif's program `rawLink us sc` (`RawScopingOk`).
-/

namespace Front

open Clif E2E.LinkCheck Link
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Opt.Legalize128

/-- **The shipped executable compiler refines the frontend bundle's program, memory faults
included** (the trap half of `bundle_correct_source_memtrap` with the `MapRelRW` premise): a trap
of the units' program's run (without load/store traps; atomic traps allowed), under the target's
run premise `TrapsExplicitM` and the memory map premise `MapFaults mp` at every fuel, makes the
fault-aware executable machine `stepF mp` run from `r` to a trap site of the entry function with
the same code whose instruction errs (`udf`) or faults under `mp`, with no faulting step before
it (`ExecTrapF`). -/
theorem bundle_correct_source_memtrapF_rw {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup
      S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (M : Nat) (mp : ArmFault.MemMap)
    (hmap : MapRelRW mp S.inputCleanup (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args' cs'.mem)
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem) :
    (∀ K, TrapsExplicitM (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs') →
    Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
    Clif.runLoop E (link us sc) M cs = .trapped c →
    ExecTrapF mp S.inputCleanup B file (legalize (f.rename σ.fwd)) c r := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source_memtrapF_rw (cs := cs.ren σ) h hsrc B hB hH
    hlegal hsig hf' hc hX ho hr M mp hmap (clifEntry_ren hcs) (by simpa using hexp)
    (by simpa using hsl) hmem (by rw [hP, hE]; exact bnd_ren hbnd)
  intro htr hnmt c hrun
  have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
  rw [← hE, ← hP] at this
  exact H htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **`bundle_correct_source_memtrapF_rw`, recursive programs included** (the trap half of
`bundle_correct_source_memtrap_peak` with the `MapRelRW` premise): the stack
`frameDrop + (D * d + pbMax)` (#581: the deepest activation's stack probes write up to `pbMax`
bytes below its frame) from the units' run's
call depth `d`; the target's run premises of the callees running with fuel `F` and at most `d - 1`
callers of their own, at every fuel. -/
theorem bundle_correct_source_memtrapF_rw_peak {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r
      args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (M : Nat) (mp : ArmFault.MemMap)
    (hmap : MapRelRW mp S.inputCleanup (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r
      args' cs'.mem)
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (link us sc) d cs) :
    (∀ F, TrapsExplicitM (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
    Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
    Clif.runLoop E (link us sc) M cs = .trapped c →
    ExecTrapF mp S.inputCleanup B file (legalize (f.rename σ.fwd)) c r := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source_memtrapF_rw_peak (cs := cs.ren σ) h hsrc B hB hH
    hlegal hsig hf' d hX ho hr M mp hmap (clifEntry_ren hcs) (by simpa using hexp)
    (by simpa using hsl) hmem (by rw [hP, hE]; exact bnd_ren hbnd)
    (by rw [hP, hE]; exact depthLe_ren hd)
  intro htr hnmt c hrun
  have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
  rw [← hE, ← hP] at this
  exact H htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **The shipped executable compiler refines cg_clif's program, memory faults included**: as
`bundle_correct_source_memtrapF_rw`, about the runs of cg_clif's program `rawLink us sc` under a
naming `sc` of its module identities that respects its declarations (`RawScopingOk`). -/
theorem bundle_correct_raw_memtrapF_rw {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup
      S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.inputCleanup (BinCheck.roByte S.inputCleanup S.data) (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (M : Nat) (mp : ArmFault.MemMap)
    (hmap : MapRelRW mp S.inputCleanup (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args' cs'.mem)
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem) :
    (∀ K, TrapsExplicitM (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs') →
    Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
    Clif.runLoop E (rawLink us sc) M cs = .trapped c →
    ExecTrapF mp S.inputCleanup B file (legalize (f.rename σ.fwd)) c r := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd ⊢
  exact bundle_correct_source_memtrapF_rw hb h hsrc hus hσ E B hE hB hH hlegal hsig hf hc hX
    ho hr M mp hmap hcs hexp hsl hmem hbnd

/-- **The shipped executable compiler refines cg_clif's program, memory faults and recursive
programs included**: as `bundle_correct_source_memtrapF_rw_peak`, about the runs of cg_clif's program
`rawLink us sc` (`RawScopingOk`). -/
theorem bundle_correct_raw_memtrapF_rw_peak {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r
      args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (M : Nat) (mp : ArmFault.MemMap)
    (hmap : MapRelRW mp S.inputCleanup (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r
      args' cs'.mem)
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (rawLink us sc) d cs) :
    (∀ F, TrapsExplicitM (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
    Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
    Clif.runLoop E (rawLink us sc) M cs = .trapped c →
    ExecTrapF mp S.inputCleanup B file (legalize (f.rename σ.fwd)) c r := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd hd ⊢
  exact bundle_correct_source_memtrapF_rw_peak hb h hsrc hus hσ E B hE hB hH hlegal hsig hf d
    hX ho hr M mp hmap hcs hexp hsl hmem hbnd hd

end Front
