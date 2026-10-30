import FV.E2E.LinkArmTwinCE
import FV.E2E.DeadCleanupBinaryInitRU

/-!
# The binary-level theorems under the slot-byte oracle, corrected premises (SEM1 #537, #719, #716)

`InitOk` (`DeadCleanupBinaryInit`) bundles `DetPRB`, which is false for real programs (#719), and
`DetTabPRBE`, `DetTabPRBr`. **`InitOkR`**: the same scope conditions with the corrected
determinism `DetPRBR` (#719) and the call twins `CallTwinCE` (#716), from which `DetTabPRBE`
(`detTabPRBE_ofCE`) and `DetTabPRBr` (`detTabPRBr_ofCE`) follow.

* `InitOkR`, `InitOkR.detTab`, `InitOkR.detTabR`;
* **`binary_correct_initR`**: `binary_correct_init` under `InitOkR`;
* **`binary_correct_initTR`**: a trapping whole-program CLIF run (its traps explicit) from the
  reference entry placed with the machine's own table is realised by the linked machine from the
  model state (`backend_correct_program_initETR`);
* `model_init_sysSR`, **`binary_correct_exec_initR`**: `binary_correct_exec_init` under
  `InitOkR`.

`InitOkR` cannot be constructed (#732: `DetPRBR` is false when the canonical return list names
`x30`); every theorem here is a corollary of its `InitOkRU` form (`DeadCleanupBinaryInitRU`,
`InitOkR.toU`).
-/

namespace E2E.DeadCleanupBinary
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck

/-- **The premises of the oracle route, corrected** (module doc): the scope conditions
`BaseRetOk`, `RetCount`, `HooksKeep`, the determinism `DetPRBR` (#719) and the call twins
`CallTwinCE` (#716) of the linked system `L` with budget `κ`. -/
structure InitOkR (L : LinkSys) (κ : Nat → Clif.Function → Nat) : Prop where
  baseRet : L.BaseRetOk
  retCount : ∀ g ∈ L.P.funcs, L.RetCount g
  det : ∀ M, L.std.DetPRBR κ M
  twin : ∀ M, L.std.CallTwinCE κ M
  hooks : L.HooksKeep

theorem InitOkR.detTab {L : LinkSys} {κ : Nat → Clif.Function → Nat} (h : InitOkR L κ) (M : Nat) :
    L.std.DetTabPRBE κ M :=
  L.std.detTabPRBE_ofCE (h.twin M)

theorem InitOkR.detTabR {L : LinkSys} {κ : Nat → Clif.Function → Nat} (h : InitOkR L κ)
    (M : Nat) : L.std.DetTabPRBr κ M :=
  L.std.detTabPRBr_ofCE (h.twin M)

/-- **`InitOkR` gives `InitOkRU`** (`DetPRBR.toU`; the fields hold without `NeedSlots`). -/
theorem InitOkR.toU {L : LinkSys} {κ : Nat → Clif.Function → Nat} (h : InitOkR L κ) :
    InitOkRU L κ :=
  ⟨fun _ => h.baseRet, fun _ => h.retCount, fun _ M => LinkSys.DetPRBR.toU L.std (h.det M),
    fun _ => h.detTab, fun _ => h.detTabR, fun _ => h.hooks⟩

/-- **`binary_correct_init` under `InitOkR`** (module doc). -/
theorem binary_correct_initR {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : DeadCleanupStackBound.goodN I n = true)
    {f : Clif.Function} (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOkR (sysW I B f r) (kapW I B f r))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (.returned vals cm) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) ∧
    (sys I B).RunGoodL M f (modelOf I f r) :=
  binary_correct_initRU hbin B hB hn hf M hX ho hr hIO.toU hrun

/-- **The binary-level theorem under the slot-byte oracle, trapping runs** (module doc): a
trapping whole-program CLIF run whose traps are explicit, from the reference entry placed with the
machine's own slot table, is realised by the linked machine from the model state. -/
theorem binary_correct_initTR {I : LinkInput} {X : Image} {R : BitVec 64 → Prop}
    {roB : BitVec 64 → Option (BitVec 8)} (hbin : BinFacts I X R roB) (B : BaseEnv)
    (hB : BaseOk (sys I B)) {n : String} (hn : DeadCleanupStackBound.goodN I n = true)
    {f : Clif.Function} (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState}
    {args : List Clif.Val} {cs : Clif.State} (hX : X.Intact r)
    (ho : OutsideCall I roB f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOkR (sysW I B f r) (kapW I B f r))
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) {c : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (.trapped c) ∧
    (∀ a, (modelOf I f r).mem a ≠ r.mem a → R a) :=
  binary_correct_initTRU hbin B hB hn hf M hX ho hr hIO.toU htr hrun

end E2E.DeadCleanupBinary

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **`model_init_sysS` under `InitOkR`.** -/
theorem model_init_sysSR {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hbin : E2E.DeadCleanupBinCheck.BinOk I D file) (hB : BaseOk (sys I B)) {n : String}
    (hn : DeadCleanupStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOkR (sysS I B f r S) (kapW I B f r))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (.returned vals cm) ∧
    (sysS I B f r S).RunGoodL M f (modelOf I f r) :=
  model_init_sysSRU hI hbin hB hn hf M hX ho hav hr hIO.toU hrun

/-- **`binary_correct_exec_init` under `InitOkR`** (module doc): the executable machine run from
`r` refines a returning whole-program CLIF run from the reference entry placed with the machine's
own slot table. -/
theorem binary_correct_exec_initR {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hcm : codeMapB I (tabOf I.resultsCleanup) = true)
    (hbin : DeadCleanupBinCheck.BinOk I D file) (hgot : GotOk I file) (B : BaseEnv)
    (hB : BaseOk (sys I B)) (hH : HooksSim I B) {n : String} {f : Clif.Function}
    (hf : (prog I).func? n = some f)
    (hc : ¬ DeadCleanupStackBound.CycleFrom (DeadCleanupStackBound.Calls I I.resultsCleanup) f)
    (M : Nat) {r : Arm.ArmState} {args : List Clif.Val} {cs : Clif.State}
    (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hav : OutsideAvoids (GotSlot I file) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOkR (sysS I B f r (GotSlot I file)) (kapW I B f r))
    {vals : List Clif.Val} {cm : Clif.Mem}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .returned vals cm) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (.returned vals cm) :=
  binary_correct_exec_initRU hI hcm hbin hgot B hB hH hf hc M hX ho hav hr hIO.toU hrun

end E2E.DeadCleanupExecBytes
