import FV.Concurrency.CallEnterArm
import FV.Concurrency.LinkedMachineWitness
import FV.Concurrency.CallRetPremisesWitness

/-!
# Witness: the callee entered on the linked machine (#473, step (3))

On the link of the compiled caller and the compiled `atomic_load` (`LinkedMachine.Witness.link2`),
the caller's activation at its `call` item (`sBF`, `Q` there by `qC1`):

* `static_ld`: the callee is statically checked (`LFn.Static`);
* **`step_call_C`**: `Link.step_call`: the machine steps the `bl` into `atomic_load` (`enterL`),
  without events;
* **`enter_call_L`**: `Link.enter_call`: the callee's activation entered there (no callee budget,
  the caller's addresses `RC.F` kept) is `Wf`, its entry an `AbiCall` returning after the `bl`,
  and `Q`/`AInv` hold after its prologue.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.LinkedMachine.Witness

open Arm ArmThread ArmInstFoot Backend Backend.Proof E2E ArmAllocThread CallSeg.WitnessC
  CallResumeL.Witness CallRetResume CallRetResume.Witness RealizeCompiled.WitnessL
open ArmAllocThread.Witness (act)

theorem dest_C1 : infoC1.dest = .sym "ld" := by native_decide

theorem entryArg_ld : ∀ r, ldF.vc.EntryArg r → r.isArgReg = true := by
  rintro r ⟨vb, ds, h1, h2, v, hv⟩
  have h : entryArgsB vcpL = true := entryArgsL
  simp only [entryArgsB, show vcpL = ldF.vc from rfl, h1, h2, List.all_eq_true] at h
  exact h _ hv

/-- The compiled `atomic_load` is statically checked. -/
theorem static_ld : ldF.Static := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  have hW := wfX (q_stRel hq)
  exact ⟨hW.check, hW.alloc, hW.emit, hW.layout, hW.lm, hW.fit, hW.psF, entryArg_ld⟩

/-- The caller's activation in the link is `RC` but for its hooks. -/
theorem wf_C : (link2.act callerF sC0 0 GL).Wf :=
  ⟨wfRC.check, wfRC.alloc, wfRC.emit, wfRC.layout, wfRC.lm, wfRC.fit, wfRC.stack, wfRC.psF,
    wfRC.prog0, wfRC.gfree⟩

/-- **The caller's `bl` on the linked machine** (module doc). -/
theorem step_call_C : link2.M sBF = enterL sBF ∧ stepEvs sBF = [] ∧ cls sBF = .plain := by
  obtain ⟨m, its, hq⟩ := qC1
  have hq' : Q (link2.act callerF sC0 0 GL) sBF
      (.run ⟨0, .op 1 #[.reg (.x 0), .reg (.x 0)] :: its, m, w₀C⟩) :=
    Q.hooks link2.H (RL.sP_hooks wfRC abiRC link2.H) hq
  exact Link.step_call ok2 (nA := "f") (nB := "ld") (FA := callerF) (FB := ldF) (by simp [link2])
    (by simp [link2]) (s0 := sC0) (K := 0) (G := GL) wf_C hq' vb0C callChecksC.1 dest_C1

/-- **The callee entered** (module doc). -/
theorem enter_call_L :
    (link2.act ldF (enterL sBF) 0 RC.F).Wf ∧
      AbiCall ldF.fb ldF.base (Arm.r .PC sBF + 4#64) (enterL sBF) ∧
      (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f (enterL sBF) = Arm.r f sBF) ∧
      xreg 30 (enterL sBF) = Arm.r .PC sBF + 4#64 ∧ (enterL sBF).mem = sBF.mem ∧
      Q (link2.act ldF (enterL sBF) 0 RC.F)
        (iterN (link2.act ldF (enterL sBF) 0 RC.F).step (prologueLines ldF.af.saves ldF.af.frameSize ldF.af.isCaller).length
          (enterL sBF))
        (MConf.init ldF.rf (locVal (link2.act ldF (enterL sBF) 0 RC.F).fr
          (iterN (link2.act ldF (enterL sBF) 0 RC.F).step (prologueLines ldF.af.saves ldF.af.frameSize ldF.af.isCaller).length
            (enterL sBF))) (bodyOf ldF.af (enterL sBF))) ∧
      AInv (link2.act ldF (enterL sBF) 0 RC.F)
        (MConf.init ldF.rf (locVal (link2.act ldF (enterL sBF) 0 RC.F).fr
          (iterN (link2.act ldF (enterL sBF) 0 RC.F).step (prologueLines ldF.af.saves ldF.af.frameSize ldF.af.isCaller).length
            (enterL sBF))) (bodyOf ldF.af (enterL sBF))) := by
  obtain ⟨m, -, hq, -⟩ := prefixF
  have hS := q_stRel hq
  exact Link.enter_call ok2 (nB := "ld") (by simp [link2]) static_ld hS.err hS.align
    (fun k w hk => by
      rw [← (abiX hS).code k w hk]
      exact read_mem_bytes_congr _ _ fun i _ => by
        show sBF.mem _ = (enterL sBF).mem _
        rw [mem_enterL])
    (stackX hS) (wfX hS).gfree

end Concurrency.LinkedMachine.Witness
