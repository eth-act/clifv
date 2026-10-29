import FV.Front.Exe
import FV.Front.RawExeContract

/-!
# The executable compiler refines the frontend bundle's program, under one runtime contract
(A5, #411)

`Front.bundle_correct_source{,_peak}` (the units' program under a scoping `sc`) take the same
seven premises as `Front.bundle_correct_raw{,_peak}` (`FV/Front/RawExe.lean`), regrouped as for
`bundle_correct_raw_contract` (`FV/Front/RawExeContract.lean`):

* `Front.EntryContract S B file g N r args` — the runtime contract (outside code, loader, caller);
* `E2E.EntryContract.ClifView` — the choice of the CLIF state that models the entry.

`OutsideCall`'s facts about the written file are derived (`E2E.EntryContract.outsideCall_of`) from
`compileExe`'s own checks (`okB_leanLink`, `binOk_leanLink`).

* `bundle_correct_source_contract{,_peak}`.
-/

namespace Front

set_option autoImplicit false

open Clif E2E.LinkCheck Link
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram E2E.EntryContract Backend Opt.Legalize128

/-- **`Front.bundle_correct_source` under the runtime contract**: the shipped executable
compiler's output refines the frontend bundle's program for an entry `n` reaching no call cycle,
when the entry meets the single runtime contract `EntryContract` (outside code, loader, caller)
with `stackFn` bytes of stack, about the CLIF state `cs'` that models it (`ClifView`).
`OutsideCall`'s facts about the written file are derived
(`E2E.EntryContract.outsideCall_of`). -/
theorem bundle_correct_source_contract {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup
      S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hC : EntryContract S B file (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args')
    (hv : ClifView S.inputCleanup B (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
        (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := Link.DeadCleanup.compileExe_spec h
  exact bundle_correct_source hb h hsrc hus hσ E B hE hC.base hC.hooks hC.legal hC.sigs hf hc
    hC.loader.intact
    (outsideCall_of (Link.DeadCleanup.okB_leanLink hin hl) (Link.DeadCleanup.binOk_leanLink hl)
      hC.loader hC.caller hv)
    hv.run hcs hexp hsl hmem hbnd M

/-- **`Front.bundle_correct_source_peak` under the runtime contract** (recursive programs
included): as `bundle_correct_source_contract`, with `frameDrop + (D·d + pbMax)` bytes of stack
(#581: the deepest activation's stack probes write up to `pbMax` bytes below its frame) for the
source run's peak call depth `d`. -/
theorem bundle_correct_source_peak_contract {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} {σ : Clif.Ren}
    (hσ : link us (finOf us) = (link us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    {n : String} {f : Clif.Function} (hf : (link us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hC : EntryContract S B file (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup))
      r args')
    (hv : ClifView S.inputCleanup B (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup))
      r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem.ren σ)
    (hbnd : ∀ s', Opt.Legal.SReach E (link us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (link us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (link us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap E (link us sc) cs → ∀ c,
      Clif.runLoop E (link us sc) M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
        (art S.inputCleanup (legalize (f.rename σ.fwd))).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := Link.DeadCleanup.compileExe_spec h
  exact bundle_correct_source_peak hb h hsrc hus hσ E B hE hC.base hC.hooks hC.legal hC.sigs hf d
    hC.loader.intact
    (outsideCall_of (Link.DeadCleanup.okB_leanLink hin hl) (Link.DeadCleanup.binOk_leanLink hl)
      hC.loader hC.caller hv)
    hv.run hcs hexp hsl hmem hbnd hd M

end Front
