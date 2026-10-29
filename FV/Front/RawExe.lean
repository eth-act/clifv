import FV.Front.Exe
import FV.Front.RawProof

/-!
# The executable compiler refines cg_clif's program (T7b/T7c, docs/contracts/frontend.md)

`FV/Front/Exe.lean`'s theorems are about the decoded units' program under any scoping `sc`
(`link us sc`). By `rawLink_eq_link` the decoded program under the scoping `rawPull us sc` *is*
cg_clif's program as its dumps wrote it — functions, callees and global values named by module
identities `uNS:IDX` and libcalls — under any naming `sc` that names two of its names alike exactly
when cg_clif's module declared them as one symbol (`RawScopingOk`). So the same theorems hold with
`rawLink us sc` for the source program: the decoding (`Front.decodeFn`, formerly `normalize.py`
and `clif-data-export`'s identity recovery) is not trusted. `raw_alpha` supplies the bijection `σ`
for any such naming; `rawScoping_of` shows such namings exist (e.g. the declarations followed by
the linked names).

* `bundle_correct_raw`, `bundle_correct_raw_peak` (the shipped compiler);
* `bundle_correct_raw_baseline`, `bundle_correct_raw_peak_baseline` (the baseline compiler).
-/

namespace Front

open Clif E2E.LinkCheck Link
section Cleanup

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Opt.Legalize128
/-- **The shipped executable compiler (`bundle_correct_source`), entries without a reachable call cycle refines cg_clif's program**: as `bundle_correct_source`, about the runs of cg_clif's
program `rawLink us sc` under a naming `sc` of its module identities that respects its declarations
(`RawScopingOk`). -/
theorem bundle_correct_raw {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
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
  rw [← he] at hσ hf hbnd ⊢
  exact bundle_correct_source hb h hsrc hus hσ E B hE hB hH hlegal hsig hf hc hX ho hr hcs hexp hsl hmem hbnd M

/-- **The shipped executable compiler, recursive programs included (`bundle_correct_source_peak`) refines cg_clif's program**: as `bundle_correct_source_peak`, about the runs of cg_clif's
program `rawLink us sc` under a naming `sc` of its module identities that respects its declarations
(`RawScopingOk`). The stack is `frameDrop + (D * d + pbMax)` (#581: the deepest activation's stack
probes write up to `pbMax` bytes below its frame). -/
theorem bundle_correct_raw_peak {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
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
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
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
  rw [← he] at hσ hf hbnd hd ⊢
  exact bundle_correct_source_peak hb h hsrc hus hσ E B hE hB hH hlegal hsig hf d hX ho hr hcs hexp hsl hmem hbnd hd M

end Cleanup
section Baseline

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.Binary E2E.ExecBytes E2E.LegalProgram Backend
  Opt.Legalize128
/-- **The baseline executable compiler (`bundle_correct_source_baseline`) refines cg_clif's program**: as `bundle_correct_source_baseline`, about the runs of cg_clif's
program `rawLink us sc` under a naming `sc` of its module identities that respects its declarations
(`RawScopingOk`). -/
theorem bundle_correct_raw_baseline {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.input = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (hc : ¬ StackBound.CycleFrom (StackBound.Calls S.input S.input.results) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize (f.rename σ.fwd))
      (StackBound.stackFn S.input (legalize (f.rename σ.fwd))) r args' cs'.mem)
    (hr : ClifRun S.input B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize (f.rename σ.fwd))).fb (art S.input (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.input B file) r
          (RelocAt S.input) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.input) B.env M) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefines (art S.input (legalize (f.rename σ.fwd))).fb (art S.input (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.input B file) r
        (RelocAt S.input) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd ⊢
  exact bundle_correct_source_baseline hb h hsrc hus hσ E B hE hB hH hlegal hsig hf hc hX ho hr hcs hexp hsl hmem hbnd M

/-- **The baseline executable compiler, recursive programs included (`bundle_correct_source_peak_baseline`) refines cg_clif's program**: as `bundle_correct_source_peak_baseline`, about the runs of cg_clif's
program `rawLink us sc` under a naming `sc` of its module identities that respects its declarations
(`RawScopingOk`). The stack is `frameDrop + (D * d + pbMax)` (#581: the deepest activation's stack
probes write up to `pbMax` bytes below its frame). -/
theorem bundle_correct_raw_peak_baseline {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.input = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    (hB : BaseOk (sys S.input B)) (hH : HooksSim S.input B)
    (hlegal : (∃ f ∈ S.input.srcProg.funcs, mentions128 f = true) →
      Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env)
    (hsig : (∃ g ∈ (prog S.input).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall S.input (BinCheck.roByte S.input S.data) (legalize (f.rename σ.fwd))
      (frameDrop (art S.input (legalize (f.rename σ.fwd))).af + (S.input.D * d + pbMax S.input)) r
      args' cs'.mem)
    (hr : ClifRun S.input B (legalize (f.rename σ.fwd)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (rawLink us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.input (legalize (f.rename σ.fwd))).fb (art S.input (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.input B file) r
          (RelocAt S.input) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.input) B.env F d) (prog S.input).bare cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefines (art S.input (legalize (f.rename σ.fwd))).fb (art S.input (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.input B file) r
        (RelocAt S.input) (.trapped c)) := by
  obtain ⟨-, he⟩ := rawLink_eq_link (units_ok hus) hraw
  rw [← he] at hσ hf hbnd hd ⊢
  exact bundle_correct_source_peak_baseline hb h hsrc hus hσ E B hE hB hH hlegal hsig hf d hX ho hr hcs hexp hsl hmem hbnd hd M

end Baseline

end Front
