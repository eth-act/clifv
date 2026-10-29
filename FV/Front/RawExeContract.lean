import FV.Front.RawExe
import FV.E2E.EntryContract

/-!
# The shipped executable compiler under one runtime contract (A5, #411)

`Front.bundle_correct_raw{,_peak}` take seven premises about the code outside the program and the
entry state: `BaseOk`, `HooksSim`, the i128 helpers' contract, the indirect-call signatures,
`Image.Intact`, `OutsideCall` and `ClifRun`. Here they are regrouped by who guarantees them:

* `EntryContract S B file g N r args` — **the runtime contract**, a single structure: the code
  outside the program (`BaseOk`, `HooksSim`, `legal`, `sigs`: TO-PROVE §1.3, about `B` only), the
  OS loader (`EntryContract.Loader`: the kept bytes, `N` bytes of writable stack) and the outside
  caller (`EntryContract.Caller`: AAPCS64 entry, stack arguments in writable memory);
* `ClifView` — the choice of the CLIF state that models the entry (not an obligation).

`OutsideCall`'s fields that are facts about the written file (no code in the free stack or in a
stack argument, the read-only CLIF data's bytes) are derived (`EntryContract.outsideCall_of`) from
`compileExe`'s own checks (`okB_leanLink`, `binOk_leanLink`).

* `bundle_correct_raw_contract`, `bundle_correct_raw_peak_contract`.
-/

namespace Front

open Clif E2E.LinkCheck Link
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram Backend Opt.Legalize128 E2E.EntryContract

/-- **The runtime contract of an entry** of the executable `file` compiled from `S`, in the outside
world `B`: outside code calls the compiled function `g` in the machine state `r` with the arguments
`args` and `N` bytes of stack. Its fields are the contracts TO-PROVE §1.3 trusts by design: those of
the code outside the program (`base`, `hooks`, `legal`, `sigs`: about `B` only), of the OS loader
(`loader`) and of the outside caller (`caller`). -/
structure EntryContract (S : LinkSpec) (B : BaseEnv) (file : ByteArray) (g : Clif.Function)
    (N : Nat) (r : Arm.ArmState) (args : List Clif.Val) : Prop where
  /-- the outside world's contracts of `LinkSys.Ok` (`BaseOk`) -/
  base : BaseOk (sys S.inputCleanup B)
  /-- the outside-call and TLS hooks read no relocated instruction byte and not the program -/
  hooks : HooksSim S.inputCleanup B
  /-- programs mentioning `i128`: the outside world's helpers and externs are legal -/
  legal : (∃ f ∈ S.inputCleanup.srcProg.funcs, mentions128 f = true) →
    Opt.Legal.HelperOk B.env ∧ Opt.Legal.ExtLegal B.env ∧ Opt.Legal.EnvKeepsBounded B.env
  /-- programs with indirect calls: the outside world declares no signatures -/
  sigs : (∃ g ∈ (prog S.inputCleanup).funcs, ¬ Clif.IndFree g) → ∀ n, B.env.sigOf n = none
  /-- the OS loader: kept bytes, `N` bytes of writable stack -/
  loader : Loader file N r
  /-- the outside caller: AAPCS64 entry of `g` -/
  caller : Caller S.inputCleanup file g r args

/-- **`Front.bundle_correct_raw` under the runtime contract**: the shipped executable compiler's
output refines cg_clif's program for an entry `n` reaching no call cycle, when the entry meets the
single runtime contract `EntryContract` (outside code, loader, caller) with `stackFn` bytes of
stack, about the CLIF state `cs'` that models it (`ClifView`). `OutsideCall`'s facts about the
written file are derived (`EntryContract.outsideCall_of`). -/
theorem bundle_correct_raw_contract {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hC : EntryContract S B file (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args')
    (hv : ClifView S.inputCleanup B (legalize (f.rename σ.fwd))
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize (f.rename σ.fwd))) r args' cs')
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
  obtain ⟨hin, hl⟩ := Link.DeadCleanup.compileExe_spec h
  exact bundle_correct_raw hb h hsrc hus hraw hσ E B hE hC.base hC.hooks hC.legal hC.sigs hf hc
    hC.loader.intact
    (outsideCall_of (Link.DeadCleanup.okB_leanLink hin hl) (Link.DeadCleanup.binOk_leanLink hl)
      hC.loader hC.caller hv)
    hv.run hcs hexp hsl hmem hbnd M

/-- **`Front.bundle_correct_raw_peak` under the runtime contract** (recursive programs included):
as `bundle_correct_raw_contract`, with `frameDrop + (D·d + pbMax)` bytes of stack (#581: the
deepest activation's stack probes write up to `pbMax` bytes below its frame) for the source run's peak
call depth `d`. -/
theorem bundle_correct_raw_peak_contract {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExe S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hC : EntryContract S B file (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args')
    (hv : ClifView S.inputCleanup B (legalize (f.rename σ.fwd))
      (frameDrop (art S.inputCleanup (legalize (f.rename σ.fwd))).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs')
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
  obtain ⟨hin, hl⟩ := Link.DeadCleanup.compileExe_spec h
  exact bundle_correct_raw_peak hb h hsrc hus hraw hσ E B hE hC.base hC.hooks hC.legal hC.sigs hf d
    hC.loader.intact
    (outsideCall_of (Link.DeadCleanup.okB_leanLink hin hl) (Link.DeadCleanup.binOk_leanLink hl)
      hC.loader hC.caller hv)
    hv.run hcs hexp hsl hmem hbnd hd M

end Front
