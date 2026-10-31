import FV.Link.DeadCleanupExeTrap
import FV.E2E.EntryContract

/-!
# The shipped executable compiler with callee traps, under one runtime contract (A5, #411)

`Link.DeadCleanup.compileExe_correct_trap{,_peak}` take, beyond the runtime contract's fields
(`FV/Front/RawExeContract.lean`), the outside code's trap contract `BaseTrapsOk` and no
`try_call` terminator in the program. Here they are regrouped as for the source theorems:

* `TrapContract S B file g N r args` — **the trap contract**: the outside code's contracts
  (`BaseOk`, `HooksSim`, `BaseTrapsOk`), no `try_call` terminator in the program, the OS loader
  (`E2E.EntryContract.Loader`) and the outside caller (`E2E.EntryContract.Caller`);
* `E2E.EntryContract.ClifView` — the choice of the CLIF state that models the entry.

`OutsideCall`'s facts about the written file are derived (`E2E.EntryContract.outsideCall_of`)
from `compileExeU`'s own checks (`okB_leanLink`, `binOk_leanLink`).

* `compileExe_correct_trap_contract`, `compileExe_correct_trap_peak_contract`.
-/

namespace Link.DeadCleanup

set_option autoImplicit false

open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.EntryContract Backend Opt.Legalize128

/-- **The trap contract of an entry** (S9d): the outside code's contracts (`base`, `hooks`,
`traps`: `BaseTrapsOk`), no `try_call` terminator in the program (`noTry`, S9b), the OS loader
(`loader`) and the outside caller (`caller`). The fields are the premises of
`compileExe_correct_trap` beyond its run premise `TrapsD`. -/
structure TrapContract (S : LinkSpec) (B : BaseEnv) (file : ByteArray) (g : Clif.Function)
    (N : Nat) (r : Arm.ArmState) (args : List Clif.Val) : Prop where
  /-- the outside world's contracts of `LinkSys.Ok` (`BaseOk`) -/
  base : BaseOk (sys S.inputCleanup B)
  /-- the outside-call and TLS hooks read no relocated instruction byte and not the program -/
  hooks : HooksSim S.inputCleanup B
  /-- the outside code's trap contract: it does not return where its CLIF semantics traps -/
  traps : (sys S.inputCleanup B).BaseTrapsOk
  /-- no `try_call` terminator in the program -/
  noTry : ∀ g ∈ (prog S.inputCleanup).funcs, ∀ b ∈ g.blocks, b.term.isTry = false
  /-- the OS loader: kept bytes, `N` bytes of writable stack -/
  loader : Loader file N r
  /-- the outside caller: AAPCS64 entry of `g` -/
  caller : Caller S.inputCleanup file g r args

/-- **`compileExe_correct_trap` under the trap contract**: the shipped executable compiler's
output with callee traps, for an entry `n` of the program reaching no call cycle, when the entry
meets the trap contract `TrapContract` with `stackFn` bytes of stack, about the CLIF state `cs`
that models it (`ClifView`). `OutsideCall`'s facts about the written file are derived
(`E2E.EntryContract.outsideCall_of`). -/
theorem compileExe_correct_trap_contract {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom
      (DeadCleanupStackBound.Calls S.inputCleanup S.inputCleanup.resultsCleanup) f) (M : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hC : TrapContract S B file f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args)
    (hv : ClifView S.inputCleanup B f
      (DeadCleanupStackBound.stackFn S.inputCleanup f) r args cs)
    (htr : (sys S.inputCleanup B).std.TrapsD M f cs) :
    ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
      (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (M + 1) cs) := by
  obtain ⟨he, -⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec he
  exact compileExe_correct_trap h B hC.base hC.hooks hC.traps hC.noTry hf hc M
    hC.loader.intact
    (outsideCall_of (okB_leanLink hin hl) (binOk_leanLink hl) hC.loader hC.caller hv)
    hv.run htr

/-- **`compileExe_correct_trap_peak` under the trap contract** (recursive programs included):
as `compileExe_correct_trap_contract`, with `frameDrop + (D·d + pbMax)` bytes of stack (#581: the
deepest activation's stack probes write up to `pbMax` bytes below its frame) for the run's peak
call depth `d`. -/
theorem compileExe_correct_trap_peak_contract {S : LinkSpec} {file0 file : ByteArray}
    (h : compileExeU S file0 = .ok file) (B : BaseEnv) {n : String} {f : Clif.Function}
    (hf : (prog S.inputCleanup).func? n = some f) (F d : Nat)
    {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hC : TrapContract S B file f
      (frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup))
      r args)
    (hv : ClifView S.inputCleanup B f
      (frameDrop (art S.inputCleanup f).af + (S.inputCleanup.D * d + pbMax S.inputCleanup))
      r args cs)
    (hd : Clif.DepthLe B.env (prog S.inputCleanup) d cs)
    (htr : ((sys S.inputCleanup B).peak F).TrapsD d f cs) :
    ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
      (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup)
      (Clif.runLoop B.env (prog S.inputCleanup) (F + 1) cs) := by
  obtain ⟨he, -⟩ := compileExeU_spec h
  obtain ⟨hin, hl⟩ := compileExe_spec he
  exact compileExe_correct_trap_peak h B hC.base hC.hooks hC.traps hC.noTry hf F d
    hC.loader.intact
    (outsideCall_of (okB_leanLink hin hl) (binOk_leanLink hl) hC.loader hC.caller hv)
    hv.run hd htr

end Link.DeadCleanup
