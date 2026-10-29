import FV.Front.RawExeTrap
import FV.Front.RawExeContract

/-!
# The executable compiler refines cg_clif's program, callee traps included, under one runtime
contract (A5, #411)

`Front.bundle_correct_raw_trap{,_peak}` (`FV/Front/RawExeTrap.lean`) take, beyond the runtime
contract's fields (`Front.EntryContract`, `FV/Front/RawExeContract.lean`), the outside code's trap
contract `BaseTrapsOk` and no `try_call` terminator in the program. Here they are regrouped:

* `TrapContract S B file g N r args` — **the trap contract**: the runtime contract `EntryContract`
  plus the outside code's trap contract (`traps`: `BaseTrapsOk`) and no `try_call` terminator in
  the program (`noTry`, S9b);
* `E2E.EntryContract.ClifView` — the choice of the CLIF state that models the entry.

`OutsideCall`'s facts about the written file are derived (`E2E.EntryContract.outsideCall_of`) from
`compileExeU`'s own checks (`okB_leanLink`, `binOk_leanLink`).

* `bundle_correct_raw_trap_contract`, `bundle_correct_raw_trap_peak_contract`.
-/

namespace Front

set_option autoImplicit false

open Clif E2E.LinkCheck Link
open E2E E2E.LinkCheck E2E.BinCheck E2E.Elf E2E.DeadCleanupBinary E2E.DeadCleanupExecBytes
  E2E.LegalProgram E2E.EntryContract Backend Opt.Legalize128

/-- **The trap contract of an entry** (S9d): the runtime contract `EntryContract`
(`FV/Front/RawExeContract.lean`) plus the outside code's trap contract (`BaseTrapsOk`) and no
`try_call` terminator in the program (S9b). -/
structure TrapContract (S : LinkSpec) (B : BaseEnv) (file : ByteArray) (g : Clif.Function)
    (N : Nat) (r : Arm.ArmState) (args : List Clif.Val) : Prop extends EntryContract S B file g
    N r args where
  /-- the outside code's trap contract: it does not return where its CLIF semantics traps -/
  traps : (sys S.inputCleanup B).BaseTrapsOk
  /-- no `try_call` terminator in the program -/
  noTry : ∀ g ∈ (prog S.inputCleanup).funcs, ∀ b ∈ g.blocks, b.term.isTry = false

/-- **`Front.bundle_correct_raw_trap` under the trap contract**: the shipped executable
compiler's output refines cg_clif's program with callee traps, for an entry `n` reaching no call
cycle, when the entry meets the trap contract `TrapContract` (runtime contract, `BaseTrapsOk`, no
`try_call`) with `stackFn` bytes of stack, about the CLIF state `cs'` that models it (`ClifView`).
`OutsideCall`'s facts about the written file are derived
(`E2E.EntryContract.outsideCall_of`). -/
theorem bundle_correct_raw_trap_contract {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls S.inputCleanup
      S.inputCleanup.resultsCleanup) (legalize (f.rename σ.fwd)))
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hC : TrapContract S B file (legalize (f.rename σ.fwd))
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
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ K, (sys S.inputCleanup B).std.TrapsD K (legalize (f.rename σ.fwd)) cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := Link.DeadCleanup.compileExe_spec (Link.DeadCleanup.compileExeU_spec h).1
  exact bundle_correct_raw_trap hb h hsrc hus hraw hσ E B hE hC.base hC.hooks hC.traps hC.noTry
    hC.legal hC.sigs hf hc hC.loader.intact
    (outsideCall_of (Link.DeadCleanup.okB_leanLink hin hl) (Link.DeadCleanup.binOk_leanLink hl)
      hC.loader hC.caller hv)
    hv.run hcs hexp hsl hmem hbnd M

/-- **`Front.bundle_correct_raw_trap_peak` under the trap contract** (recursive programs
included): as `bundle_correct_raw_trap_contract`, with `frameDrop + (D·d + pbMax)` bytes of stack
(#581: the deepest activation's stack probes write up to `pbMax` bytes below its frame) for the
source run's peak call depth `d`. -/
theorem bundle_correct_raw_trap_peak_contract {b : Bundle} {S : LinkSpec} {file0 file : ByteArray}
    (hb : buildSpec b = .ok S) (h : Link.DeadCleanup.compileExeU S file0 = .ok file)
    (hsrc : SrcScopeB S.inputCleanup = true)
    {us : List PCgu} (hus : b.units.mapM parseUnit = .ok us)
    {sc : Nat → String → String} (hraw : RawScopingOk us sc) {σ : Clif.Ren}
    (hσ : link us (finOf us) = (rawLink us sc).rename σ.fwd)
    (E : Clif.Env) (B : BaseEnv) (hE : B.env = E.ren σ)
    {n : String} {f : Clif.Function} (hf : (rawLink us sc).func? n = some f) (d : Nat)
    {r : Arm.ArmState} {args args' : List Clif.Val} {cs cs' : Clif.State}
    (hC : TrapContract S B file (legalize (f.rename σ.fwd))
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
    (hbnd : ∀ s', Opt.Legal.SReach E (rawLink us sc) cs s' → Opt.Legal.MemBounded s'.mem)
    (hd : Clif.DepthLe E (rawLink us sc) d cs)
    (M : Nat) :
    (∀ vals cm, Clif.runLoop E (rawLink us sc) M cs = .returned vals cm →
      ∃ vals', Opt.Legal.ExpRel ((Opt.Legal.groups f.sig.returns).getD []) vals vals' ∧
        ExecRefines (art S.inputCleanup (legalize (f.rename σ.fwd))).fb
          (art S.inputCleanup (legalize (f.rename σ.fwd))).base
          (xreg 30 r) (step S.inputCleanup B file) r
          (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.returned vals' (cm.ren σ))) ∧
    ((∀ F, ((sys S.inputCleanup B).peak F).TrapsD d (legalize (f.rename σ.fwd)) cs') →
      Opt.Legal.NoMemTrap E (rawLink us sc) cs → ∀ c,
      Clif.runLoop E (rawLink us sc) M cs = .trapped c →
      ExecRefinesC S.inputCleanup B (xreg 30 r) (step S.inputCleanup B file) r
        (E2E.DeadCleanupBinCheck.RelocAt S.inputCleanup) (.trapped c)) := by
  obtain ⟨hin, hl⟩ := Link.DeadCleanup.compileExe_spec (Link.DeadCleanup.compileExeU_spec h).1
  exact bundle_correct_raw_trap_peak hb h hsrc hus hraw hσ E B hE hC.base hC.hooks hC.traps
    hC.noTry hC.legal hC.sigs hf d hC.loader.intact
    (outsideCall_of (Link.DeadCleanup.okB_leanLink hin hl) (Link.DeadCleanup.binOk_leanLink hl)
      hC.loader hC.caller hv)
    hv.run hcs hexp hsl hmem hbnd hd M

end Front
