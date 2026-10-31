import FV.Concurrency.CallThreadWitness
import FV.Concurrency.CallXClosedWitness
import FV.Concurrency.RealizeWitnessRmw
import FV.Concurrency.RealizeWitnessCas

/-!
# The ABI entry and the callee contract of the compiled `atomic_rmw` and `atomic_cas` (T2h, #311, calls)

On the compiled `atomic_rmw.i64 add` (`RealizeCompiled.WitnessR.RAR`, CLIF entry state `csR`)
and the compiled `atomic_cas.i64` (`RealizeCompiled.WitnessC.RAC`, entry state `csC`):

* `abiRR` / `abiRC`: their activations are entered at their ABI entries; `bodyRR` / `bodyRC`
  (as `ArmAllocEntryWitness`'s `abiRL`, `bodyRL`);
* `compiledE_R` / `compiledE_C`: every premise of `CallThread.CompiledE` (as `compiledE_L`);
* `armStepX_programR` / `step_programR` (the activation's machine keeps the program),
  `wordLdxR` / `wordLdxC` (every word that is a load exclusive acquires, with non-`sp` base;
  so `LdxAcq` at every state holding the program),
  **`funReal_rmw` / `funReal_cas`**: `CallSeg.funReal_calleeX` for the two, entered with the open
  monitor (their programs pass the `LdxAcq` check, their hooks keep the error).
-/

namespace Concurrency.CallThread.Witness

open Arm ArmFoot ArmThread Prog ClifThread ProgE2E Backend Backend.Proof VCodeThread PrepThread
  AllocThread ThreadRefine ArmAllocThread E2E ArmInstFoot RealizeCompiled RealizeCompiled.WitnessR
  RealizeCompiled.WitnessC
open Concurrency.CallSeg Concurrency.CallSeg.WitnessX

/-! ## The ABI entry -/

theorem abiRR : AbiCall RAR.fb RAR.base 0x4000#64 RAR.s0 :=
  ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsR.2.2.2.2.2.2.2.1 codeRR

theorem bodyRR : BodyEntryW RAR.F RAR.vc.EntryArg RAR.af RAR.s0 w₀R :=
  (E2E.Binary.bodyEntry_bodyOf RAR.af RAR.s0).w RAR.F entryArgRR

theorem abiRC : AbiCall RAC.fb RAC.base 0x4000#64 RAC.s0 :=
  ArmAllocThread.Witness.abi_ofAt (by decide) (by decide) factsC.2.2.2.2.2.2.2.1 codeRC

theorem bodyRC : BodyEntryW RAC.F RAC.vc.EntryArg RAC.af RAC.s0 w₀C :=
  (E2E.Binary.bodyEntry_bodyOf RAC.af RAC.s0).w RAC.F entryArgRC

/-! ## The callee contract -/

/-- **Every premise of `CompiledE`** for the compiled `atomic_rmw`. -/
theorem compiledE_R (env : Clif.Env) (p : Clif.Program) : CompiledE env p RAR csR := by
  obtain ⟨-, hq, hA⟩ := q_init_lines wfRR abiRR bodyRR
  exact ⟨wfRR, scopeLSR, rfl, ⟨_, abiRR⟩, (compiled_ofR hq hA env p).front,
    ProbeF.of_small (by have := factsR.2.2.2.2.2.2.1; omega)⟩

/-- **Every premise of `CompiledE`** for the compiled `atomic_cas`. -/
theorem compiledE_C (env : Clif.Env) (p : Clif.Program) : CompiledE env p RAC csC := by
  obtain ⟨-, hq, hA⟩ := q_init_lines wfRC abiRC bodyRC
  exact ⟨wfRC, scopeLSC, rfl, ⟨_, abiRC⟩, (compiled_ofC hq hA env p).front,
    ProbeF.of_small (by have := factsC.2.2.2.2.2.2.1; omega)⟩

/-- The machine of an activation keeps the program when its hooks do. -/
theorem armStepX_programR (s : ArmState) : (RAR.step s).program = s.program :=
  CallThread.Witness.armStepX_program (fun _ _ => rfl) (fun _ _ _ => rfl) s

theorem step_programR (s : ArmState) : (RAR.step s).program = s.program :=
  armStepX_programR s

theorem armStepX_programC (s : ArmState) : (RAC.step s).program = s.program :=
  CallThread.Witness.armStepX_program (fun _ _ => rfl) (fun _ _ _ => rfl) s

theorem step_programC (s : ArmState) : (RAC.step s).program = s.program :=
  armStepX_programC s

/-- Every word that is a load exclusive acquires, with non-`sp` base (as `CallSeg.WitnessX`
checks of the programs). -/
theorem wordLdxR : (RAR.s0.program).all (fun q => wordLdxB q.2) = true := by
  native_decide

theorem wordLdxC : (RAC.s0.program).all (fun q => wordLdxB q.2) = true := by
  native_decide

/-- **`funReal_calleeX` for the compiled `atomic_rmw`** (module doc). -/
theorem funReal_rmw (env : Clif.Env) (p : Clif.Program)
    (ext : List (Clif.Frame × List Clif.ValueId)) {M : ArmState → ArmState}
    (hM : ∀ s, s.program = RAR.s0.program → M s = RAR.step s) :
    CallCompose.FunReal env p (PrivA RAR) M (OkPriv RAR) (fun _ _ _ _ => False)
      (CalleeEnd env p RAR ext) (RAR.s0, none) (.run (ClifLift.pushC ext csR)) :=
  funReal_calleeX (compiledE_R env p) ext hM (fun s h => (step_programR s).trans h)
    (fun s _ h => armStepX_err (fun _ _ h => h) (fun _ _ _ h => h) s h)
    (fun s hs => ldxAcq_of_words wordLdxR s hs)

/-- **`funReal_calleeX` for the compiled `atomic_cas`** (module doc). -/
theorem funReal_cas (env : Clif.Env) (p : Clif.Program)
    (ext : List (Clif.Frame × List Clif.ValueId)) {M : ArmState → ArmState}
    (hM : ∀ s, s.program = RAC.s0.program → M s = RAC.step s) :
    CallCompose.FunReal env p (PrivA RAC) M (OkPriv RAC) (fun _ _ _ _ => False)
      (CalleeEnd env p RAC ext) (RAC.s0, none) (.run (ClifLift.pushC ext csC)) :=
  funReal_calleeX (compiledE_C env p) ext hM (fun s h => (step_programC s).trans h)
    (fun s _ h => armStepX_err (fun _ _ h => h) (fun _ _ _ h => h) s h)
    (fun s hs => ldxAcq_of_words wordLdxC s hs)

end Concurrency.CallThread.Witness
