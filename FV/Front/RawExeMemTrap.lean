import FV.Front.Exe
import FV.Front.RawProof
import FV.Link.DeadCleanupExeMemTrap

/-!
# The shipped executable compiler refines cg_clif's program, memory traps included (A3, #412, F7)

`docs/plans/memfault.md`. `FV/Front/RawExe.lean`'s trap halves take `TrapsExplicit` of the
compiled program's run (no load, store or atomic traps). Here a trapping atomic (`atomic_rmw`,
`atomic_cas`: their CLIF trap is an access outside every live allocation, Cranelift's
`heap_oob`) of the entry function may trap: the run premise `TrapsExplicitM` and the memory map
premise `MapFaults mp` (every such access has a byte the process's memory map `mp` does not map;
the null page, below `vm.mmap_min_addr`, for an access at address 0) replace `TrapsExplicit`, and
the observable is `ExecRefinesM`: a trap site of the entry function with the code whose
instruction errs (`udf`) or faults under `mp` (the trapping atomic's `ldaxr`).

What this claims: **if** the executable's run reaches the trapping atomic, its `ldaxr` faults
under the map. The machine's memory is total, so the theorem does not say that no earlier access
of the run faults under `mp` (slice F8). Witness: `FV/Link/DeadCleanupExeMemTrapWitness.lean`.

* `bundle_correct_source_memtrap{,_peak}`: the units' program under a scoping `sc`;
* `bundle_correct_raw_memtrap{,_peak}`: cg_clif's program `rawLink us sc` (`RawScopingOk`).
-/

namespace Front

open Clif E2E.LinkCheck Link
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Opt.Legalize128

/-- **The shipped executable compiler refines the frontend bundle's program, memory traps
included** (`bundle_correct_source` with `Link.DeadCleanup.compileExe_correct_source_memtrap`): a
return as there; a trap of the units' program's run (without load/store traps; atomic traps
allowed), under the target's run premise `TrapsExplicitM` and the memory map premise
`MapFaults mp` at every fuel, is an executable state at a trap site of the entry function with the
same code whose instruction errs (`udf`) or faults under `mp` (`ExecRefinesM`). -/
theorem bundle_correct_source_memtrap {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) (mp : ArmFault.MemMap) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ K, TrapsExplicitM (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefinesM mp S.inputCleanup file (legalize (f.rename σ.fwd)) (xreg 30 r)
        (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
        (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source_memtrap (cs := cs.ren σ) h hsrc B hB hH
    hlegal hsig hf' hc hX ho hr (clifEntry_ren hcs) (by simpa using hexp)
    (by simpa using hsl) hmem (by rw [hP, hE]; exact bnd_ren hbnd) M mp
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **`bundle_correct_source_memtrap`, recursive programs included** (with
`Link.DeadCleanup.compileExe_correct_source_memtrap_peak`): the stack from the units' run's call
depth `d`; the target's run premises of the callees running with fuel `F` and at most `d - 1`
callers of their own, at every fuel. -/
theorem bundle_correct_source_memtrap_peak {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af + S.inputCleanup.D * d) r
      args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (link us sc) d cs)
    (M : Nat) (mp : ArmFault.MemMap) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicitM (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefinesM mp S.inputCleanup file (legalize (f.rename σ.fwd)) (xreg 30 r)
        (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
        (.trapped c)) := by
  have hP : S.inputCleanup.srcProg = (link us sc).rename σ.fwd := by
    obtain ⟨us', hus', -, hs⟩ := buildSpec_srcProg hb
    rw [hus] at hus'; cases hus'
    rw [← hσ, ← hs]; rfl
  have hf' : S.inputCleanup.srcProg.func? (σ.fwd n) = some (f.rename σ.fwd) := by
    rw [hP, Clif.Program.rename_func?, hf]; rfl
  have H := Link.DeadCleanup.compileExe_correct_source_memtrap_peak (cs := cs.ren σ) h hsrc B hB hH
    hlegal hsig hf' d hX ho hr (clifEntry_ren hcs) (by simpa using hexp)
    (by simpa using hsl) hmem (by rw [hP, hE]; exact bnd_ren hbnd)
    (by rw [hP, hE]; exact depthLe_ren hd) M mp
  simp only [Clif.Function.rename_sig] at H
  refine ⟨fun vals cm hrun => ?_, fun htr hnmt c hrun => ?_⟩
  · have := Clif.runLoop_ren_returned σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.1 vals (cm.ren σ) this
  · have := Clif.runLoop_ren_trapped σ E (link us sc) M cs hrun
    rw [← hE, ← hP] at this
    exact H.2 htr (by have := noMemTrap_ren (σ := σ) hnmt; rwa [← hE, ← hP] at this) c this

/-- **The shipped executable compiler refines cg_clif's program, memory traps included**: as
`bundle_correct_source_memtrap`, about the runs of cg_clif's program `rawLink us sc` under a naming
`sc` of its module identities that respects its declarations (`RawScopingOk`). -/
theorem bundle_correct_raw_memtrap {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) (mp : ArmFault.MemMap) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ K, TrapsExplicitM (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvN (prog S.inputCleanup) B.env K) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesM mp S.inputCleanup file (legalize (f.rename σ.fwd)) (xreg 30 r)
        (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
        (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd ⊢
  exact bundle_correct_source_memtrap hb h hsrc hus hσ E B hE hB hH hlegal hsig hf hc hX
    ho hr hcs hexp hsl hmem hbnd M mp

/-- **The shipped executable compiler refines cg_clif's program, memory traps and recursive
programs included**: as `bundle_correct_source_memtrap_peak`, about the runs of cg_clif's program
`rawLink us sc` (`RawScopingOk`). -/
theorem bundle_correct_raw_memtrap_peak {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af + S.inputCleanup.D * d) r
      args' cs'.mem)
    (hr : ClifRun S.inputCleanup B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (rawLink us sc) d cs)
    (M : Nat) (mp : ArmFault.MemMap) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicitM (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs' ∧
      MapFaults mp (Clif.linkEnvD (prog S.inputCleanup) B.env F d) (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesM mp S.inputCleanup file (legalize (f.rename σ.fwd)) (xreg 30 r)
        (step S.inputCleanup B file) r (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
        (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd hd ⊢
  exact bundle_correct_source_memtrap_peak hb h hsrc hus hσ E B hE hB hH hlegal hsig hf d
    hX ho hr hcs hexp hsl hmem hbnd hd M mp

end Front
