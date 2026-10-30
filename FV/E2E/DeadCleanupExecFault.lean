import FV.ArmFault.Step
import FV.E2E.DeadCleanupExecBytes

/-!
# The executable machine with memory faults (A3, #412, slice F8d)

`step I B file` (`FV/E2E/DeadCleanupExecBytes.lean`) runs the processor on the executable's words
(`realStep`) and the base environment's hooks at calls of outside code and at the TLS sequence.
`stepF mp I B file` is the same machine whose processor steps fault under the memory map `mp`
(`ArmFault.execF`: an instruction with a byte of its footprint `mp` does not allow sets the error
`ArmFault.memFault` and changes nothing else); the hook steps are unchanged (outside code is
outside the theorems).

* `NoFault mp I B file e`: the step from `e` does not fault (`stepF` is `step` there);
  `noFault_of_evsOk` (a processor step whose instruction's footprint `mp` allows), `noFault_hook`;
* `runX_stepF`: a run in which no step faults is the run of `step`;
* `stepF_trap`: at an executable state with `ExecTrapM` (a `udf` that errs, or an instruction that
  faults under `mp`), the next state of `stepF` is an error state.
-/

namespace E2E.DeadCleanupExecBytes
set_option autoImplicit false

open Backend Backend.Proof E2E.LinkCheck E2E.DeadCleanupBinary E2E.BinCheck

section Machine

variable (mp : ArmFault.MemMap) (I : LinkInput) (B : BaseEnv) (file : ByteArray)

/-- **The processor step with faults** on the executable's word at the pc. -/
def realStepF (s : Arm.ArmState) : Arm.ArmState :=
  match Arm.read_err s with
  | .None =>
    match (fileWord file (Arm.r .PC s)).bind Arm.decode_raw_inst with
    | some a => ArmFault.execF mp a s
    | none => Arm.w .ERR (.Other "no instruction word") s
  | _ => s

/-- The step at a site, with faults at the processor steps. -/
noncomputable def stepAtF (site : Option Site) (s : Arm.ArmState) : Arm.ArmState :=
  match site with
  | some (.extCall n) => B.hooks.call (some n) s
  | some .blr =>
    if ((blrTarget s).bind (symCallee (sys I B).Xb (prog I))).isSome then realStepF mp file s
    else B.hooks.call none s
  | some .tlsAdrp => Arm.w .PC (Arm.r .PC s + 4) s
  | some (.tls tmp n) => B.hooks.tls n tmp s
  | _ => realStepF mp file s

/-- **The executable machine with memory faults**: `step` whose processor steps fault under
`mp`. -/
noncomputable def stepF (s : Arm.ArmState) : Arm.ArmState :=
  stepAtF mp I B file (siteAt I (Arm.r .PC s)) s

/-- **The step from `e` does not fault.** -/
def NoFault (e : Arm.ArmState) : Prop := stepF mp I B file e = step I B file e

end Machine

section Lemmas

variable {mp : ArmFault.MemMap} {I : LinkInput} {B : BaseEnv} {file : ByteArray}

theorem realStepF_of_evsOk {s : Arm.ArmState}
    (h : ∀ a, Arm.r .ERR s = .None → (fileWord file (Arm.r .PC s)).bind Arm.decode_raw_inst = some a →
      ArmFault.evsOk mp (Concurrency.ArmInstFoot.instEvs a s) = true) :
    realStepF mp file s = realStep file s := by
  unfold realStepF realStep
  cases he : Arm.read_err s with
  | None =>
    simp only
    cases ha : (fileWord file (Arm.r .PC s)).bind Arm.decode_raw_inst with
    | none => rfl
    | some a => exact ArmFault.execF_of_ok (h a he ha)
  | _ => rfl

/-- **No fault at a processor step whose instruction's footprint `mp` allows.** -/
theorem noFault_of_evsOk {e : Arm.ArmState}
    (h : ∀ a, Arm.r .ERR e = .None → (fileWord file (Arm.r .PC e)).bind Arm.decode_raw_inst = some a →
      ArmFault.evsOk mp (Concurrency.ArmInstFoot.instEvs a e) = true) :
    NoFault mp I B file e := by
  unfold NoFault stepF step stepAtF stepAt
  rw [realStepF_of_evsOk h]
  rfl

/-- No fault at a step that is no processor step. -/
theorem noFault_of_site {e : Arm.ArmState}
    (h : (∃ n, siteAt I (Arm.r .PC e) = some (.extCall n)) ∨
      siteAt I (Arm.r .PC e) = some .tlsAdrp ∨ (∃ tmp n, siteAt I (Arm.r .PC e) = some (.tls tmp n)) ∨
      (siteAt I (Arm.r .PC e) = some .blr ∧
        ((blrTarget e).bind (symCallee (sys I B).Xb (prog I))).isSome = false)) :
    NoFault mp I B file e := by
  unfold NoFault stepF step
  rcases h with ⟨n, hn⟩ | hn | ⟨tmp, n, hn⟩ | ⟨hn, hb⟩ <;> rw [hn] <;> simp [stepAtF, stepAt, *]

/-- **A run in which no step faults is the run of `step`.** -/
theorem runX_stepF {e : Arm.ArmState} :
    ∀ {k : Nat}, (∀ j < k, NoFault mp I B file (runX (step I B file) j e)) →
      runX (stepF mp I B file) k e = runX (step I B file) k e
  | 0, _ => rfl
  | k + 1, h => by
    rw [runX_succ', runX_succ', runX_stepF fun j hj => h j (by omega)]
    exact h k (by omega)

/-- **At an erring or faulting processor step, the machine with faults errs.** -/
theorem stepF_err {e : Arm.ArmState} (herr : Arm.r .ERR e = .None)
    (hsite : siteAt I (Arm.r .PC e) = some .real) {a : Arm.ArmInst}
    (ha : (fileWord file (Arm.r .PC e)).bind Arm.decode_raw_inst = some a)
    (h : Arm.r .ERR (Arm.exec_inst a e) ≠ .None ∨ ArmFault.InstFaults mp a e) :
    Arm.r .ERR (stepF mp I B file e) ≠ .None := by
  have hs : stepF mp I B file e = ArmFault.execF mp a e := by
    unfold stepF stepAtF realStepF
    rw [hsite]
    simp only [show Arm.read_err e = .None from herr, ha]
  rw [hs]
  by_cases hf : ArmFault.InstFaults mp a e
  · rw [ArmFault.execF_fault hf]
    simp only [Arm.write_err, Arm.r_of_w_same]
    exact ArmFault.memFault_ne_none
  · rw [ArmFault.execF_of_not hf]
    exact h.resolve_right hf

end Lemmas

end E2E.DeadCleanupExecBytes
