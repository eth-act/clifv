import FV.Link.DeadCleanupExeSource
import FV.E2E.EntryContract

/-!
# The shipped executable compiler refines the original source program, under one runtime contract
(A5, #411)

`Link.DeadCleanup.compileExe_correct_source{,_peak}` take seven premises about the code outside
the program and the entry state: `BaseOk`, `HooksSim`, the i128 helpers' contract, the
indirect-call signatures, `Image.Intact`, `OutsideCall` and `ClifRun`. Here they are regrouped by
who guarantees them, as for `Front.EntryContract` (`FV/Front/RawExeContract.lean`):

* `EntryContract S B file g N r args` — **the runtime contract**: the code outside the program
  (`BaseOk`, `HooksSim`, `legal`, `sigs`), the OS loader (`E2E.EntryContract.Loader`) and the
  outside caller (`E2E.EntryContract.Caller`);
* `E2E.EntryContract.ClifView` — the choice of the CLIF state that models the entry.

`OutsideCall`'s facts about the written file are derived (`E2E.EntryContract.outsideCall_of`) from
`compileExe`'s own checks (`okB_leanLink`, `binOk_leanLink`).

* `compileExe_correct_source_contract`, `compileExe_correct_source_peak_contract`.
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.EntryContract Backend Opt.Legalize128

/-- **The runtime contract of an entry** of the executable `file` compiled from `S`, in the
outside world `B`: outside code calls the compiled function `g` in the machine state `r` with the
arguments `args` and `N` bytes of stack. The same fields as `Front.EntryContract`
(`FV/Front/RawExeContract.lean`): those of the code outside the program (`base`, `hooks`, `legal`,
`sigs`), of the OS loader (`loader`) and of the outside caller (`caller`). -/
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

/-- **`compileExe_correct_source` under the runtime contract**: the shipped executable compiler's
output refines the original source program for an entry `n` reaching no call cycle, when the entry
meets the single runtime contract `EntryContract` (outside code, loader, caller) with `stackFn`
bytes of stack, about the CLIF state `cs'` that models it (`ClifView`). `OutsideCall`'s facts
about the written file are derived (`E2E.EntryContract.outsideCall_of`). -/
theorem compileExe_correct_source_contract {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) {n : String} {f : Clif.Function}
    (hf : S.inputCleanup.srcProg.func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) (legalize f))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hC : EntryContract S B file (legalize f)
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize f)) r args')
    (hv : ClifView S.inputCleanup B (legalize f)
      (DeadCleanupStackBound.stackFn S.inputCleanup (legalize f)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ M, TrapsExplicit (Clif.linkEnvN (prog S.inputCleanup) B.env M)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact compileExe_correct_source h hsrc B hC.base hC.hooks hC.legal hC.sigs hf hc
    hC.loader.intact
    (outsideCall_of (okB_leanLink hin hl) (binOk_leanLink hl) hC.loader hC.caller hv)
    hv.run hcs hexp hsl hmem hbnd M

/-- **`compileExe_correct_source_peak` under the runtime contract** (recursive programs included):
as `compileExe_correct_source_contract`, with `frameDrop + (D·d + pbMax)` bytes of stack (#581: the
deepest activation's stack probes write up to `pbMax` bytes below its frame) for the source run's
peak call depth `d`. -/
theorem compileExe_correct_source_peak_contract {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExe S file0 = .ok file) (hsrc : SrcScopeB S.inputCleanup = true)
    (B : BaseEnv) {n : String} {f : Clif.Function}
    (hf : S.inputCleanup.srcProg.func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hC : EntryContract S B file (legalize f)
      (frameDrop (art S.inputCleanup (legalize f)).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args')
    (hv : ClifView S.inputCleanup B (legalize f)
      (frameDrop (art S.inputCleanup (legalize f)).af +
        (S.inputCleanup.D * d + pbMax S.inputCleanup)) r args' cs')
    (hcs : ClifEntry f args cs)
    (hexp : Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.params).getD []) args args')
    (hsl : cs'.frame.slots = cs.frame.slots) (hmem : cs'.mem = cs.mem)
    (hbnd : ∀ s', Opt.Legal.SReach B.env S.inputCleanup.srcProg cs s' →
      Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe B.env S.inputCleanup.srcProg d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop B.env S.inputCleanup.srcProg M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' cm)) ∧
    ((∀ F, TrapsExplicit (Clif.linkEnvD (prog S.inputCleanup) B.env F d)
        (prog S.inputCleanup).bare cs') →
      Opt.Legal.NoMemTrap B.env S.inputCleanup.srcProg cs → ∀ c,
      Clif.runLoop B.env S.inputCleanup.srcProg M cs = .trapped c →
      ExecRefines (art S.inputCleanup (legalize f)).fb (art S.inputCleanup (legalize f)).base
        (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := compileExe_spec h
  exact compileExe_correct_source_peak h hsrc B hC.base hC.hooks hC.legal hC.sigs hf d
    hC.loader.intact
    (outsideCall_of (okB_leanLink hin hl) (binOk_leanLink hl) hC.loader hC.caller hv)
    hv.run hcs hexp hsl hmem hbnd hd M

end Link.DeadCleanup
