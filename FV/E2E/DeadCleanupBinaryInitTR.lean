import FV.E2E.DeadCleanupBinaryInitR
import FV.E2E.DeadCleanupBinaryInitTRU

/-!
# The executable machine on a trapping run under the slot-byte oracle (SEM1 #537)

`binary_correct_exec_initR` (`DeadCleanupBinaryInitR`) covers returning CLIF runs placed with the
machine's own slot table. With the per-state facts of a trapping run (`ThmPRBGT`,
`backend_correct_program_initETXR`) the same proof covers trapping runs (their traps explicit,
as `binary_correct_exec_proven`'s `TrapsExplicit`):

* `model_init_sysSTR`: the model's trapping run in the system keeping the slots `S`, with its
  per-state facts;
* **`binary_correct_exec_initTR`**: the executable machine run from `r` reaches the trap site of a
  trapping whole-program CLIF run (`ExecRefines … (.trapped c)`), under `InitOkR`.

Both are corollaries of their `InitOkRU` forms (`DeadCleanupBinaryInitTRU`, `InitOkR.toU`).
-/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

variable {I : LinkInput} {B : BaseEnv} {file : ByteArray}

/-- **`model_init_sysSR` for a trapping run.** -/
theorem model_init_sysSTR {D : List Clif.DataObject} (hI : okBCleanup I = true)
    (hbin : E2E.DeadCleanupBinCheck.BinOk I D file) (hB : BaseOk (sys I B)) {n : String}
    (hn : DeadCleanupStackBound.goodN I n = true) {f : Clif.Function}
    (hf : (prog I).func? n = some f) (M : Nat) {r : Arm.ArmState} {args : List Clif.Val}
    {cs : Clif.State} (hX : (imageOf file).Intact r)
    (ho : OutsideCall I (BinCheck.roByte I D) f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    {S : BitVec 64 → Prop} (hav : OutsideAvoids S f (DeadCleanupStackBound.stackFn I f) r args cs.mem)
    (hr : ClifRunB I B M f r args cs) (hIO : InitOkR (sysS I B f r S) (kapW I B f r))
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) {c : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) :
    ArmRefines (art I f).fb (art I f).base (xreg 30 r) ((sys I B).mach M f) (modelOf I f r)
      (.trapped c) ∧
    (sysS I B f r S).RunGoodL M f (modelOf I f r) :=
  model_init_sysSTRU hI hbin hB hn hf M hX ho hav hr hIO.toU htr hrun

/-- **The binary theorem about the executable's own words under the slot-byte oracle, trapping
runs** (module doc). -/
theorem binary_correct_exec_initTR {D : List Clif.DataObject} (hI : okBCleanup I = true)
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
    (htr : TrapsExplicit (Clif.linkEnvN (prog I) B.env M) (prog I).bare cs) {c : Clif.TrapCode}
    (hrun : Clif.runLoop B.env (prog I) (M + 1) cs = .trapped c) :
    ExecRefines (art I f).fb (art I f).base (xreg 30 r) (step I B file) r
      (E2E.DeadCleanupBinCheck.RelocAt I) (.trapped c) :=
  binary_correct_exec_initTRU hI hcm hbin hgot B hB hH hf hc M hX ho hav hr hIO.toU htr hrun

end E2E.DeadCleanupExecBytes
