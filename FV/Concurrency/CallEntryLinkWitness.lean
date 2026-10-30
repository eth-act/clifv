import FV.Concurrency.CallEntryLink
import FV.Concurrency.CallResumeChecksWitness
import FV.Concurrency.CallArityWitness
import FV.Concurrency.CallArgsL2Witness
import FV.Concurrency.CallArgsEntryWitness
import FV.Concurrency.CallEnterArmWitness
import FV.Concurrency.CallEntryWitness
import FV.Concurrency.CallArgsAtWitness

/-!
# Witness: the call end on the linked machine (#473, step (4))

On the link of the compiled caller and the compiled `atomic_load` (`LinkedMachine.Witness.link2`,
the caller's activation `link2.act callerF sC0 0 GL`, its CLIF function `fC`):

* `driverA_fC`: `IselResume.driverHypT_ofA` for `fC`, every premise discharged;
* **`call_end_fC`**: `Link.call_end` for the caller's call of `atomic_load` (`fL`), every premise
  holding but the paused configuration's relations, the CLIF state at the call and the callee's
  code bytes, budget and kept addresses.

Checks by `native_decide` (witness only).
-/

namespace Concurrency.LinkedMachine.Witness

open Arm ArmThread ArmInstFoot Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  AllocThread E2E ArmAllocThread CallSeg.WitnessC CallResumeL.Witness CallEntry.Witness
  IselCall.Witness CallArgsEntry CallArgsAt CallResumeChecks IselCheck CallResumeAll
open RealizeCompiled.WitnessL (fL)

theorem sig_fL : fL.sig = extF.sig := by native_decide

theorem name_extF : extF.name = "ld" := by native_decide

/-- **The driver of `fC` with the call checks** (module doc). -/
theorem driverA_fC {env : Clif.Env} (henv : env.extern "ld" = none) (c : BitVec 64) :
    ∃ ctx st0 R gn bl A,
      DriverHypT fC vcC ctx st0 R gn bl A (csem RC.F RC.ctx RC.X) (RelW ΓC fC c) env pCL ∧
      threadCheckBlC fC bl = true ∧ CallArity.callArityBl fC bl = true ∧
      callUseRegsBl fC bl = true := by
  obtain ⟨hlow, hthr, -, hnames, hind, hv, hnt, -, hout0, -, -⟩ := checksFC
  have hext : ∀ e ∈ fC.externs, env.extern e.2.name = none := by
    intro e he
    have : e.2.name ∈ fC.externs.map (·.2.name) := List.mem_map_of_mem he
    rw [hnames, List.mem_singleton] at this
    rw [this]; exact henv
  exact IselResume.driverHypT_ofA (Γ := ΓC) (fctx := RC.ctx) (X := VCodeThread.Witness.X0)
    (c := c) (env := env) (p := pCL) hlow hthr CallResumeAll.Witness.arity_fC.1
    CallArgsEntry.Witness.useRegs_fC hext (List.isEmpty_iff.mp hind) hv hnt cfgFC hout0 rfl
    (fun _ _ h => by cases h)

/-- **The call end of the caller of `atomic_load`** (module doc). -/
theorem call_end_fC {env : Clif.Env} (henv : env.extern "ld" = none) (c : BitVec 64) :
    ∃ (ctx : Ctx) (st0 : LState) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
      (A : Nat → Nat → List Clif.ValueId) (L : Nat → Prop) (ss' : Array (Array Nat))
      (cc : CheckCtx) (ins : Array (Option AState)),
      DriverHypT fC vcC ctx st0 R gn bl A (csem RC.F RC.ctx RC.X) (RelW ΓC fC c) env pCL ∧
      ∀ {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState}
        {cM' : MState CV ArmState} {slots : List (Clif.SlotId × Nat)} {stm : Clif.Stmt}
        {rest : List Clif.Stmt} {fn : Clif.FnRef} {args : List Clif.ValueId}
        {vals : List Clif.Val} {KB : Nat} {GB : BitVec 64 → Prop},
        Q (link2.act callerF sC0 0 GL) x (.run cM') →
        Pause (link2.act callerF sC0 0 GL) (.run cM') →
        Match fC ctx R gn bl A (RelW ΓC fC c) slots s' vV' →
        PMatch vcC RC.vc (csem RC.F RC.ctx RC.X) (cEvs RC.F RC.ctx) L ss' (.run vV') (.run vP') →
        MatchRun cc ins ckeep r₀ cM' vP' →
        s'.frame.body = stm :: rest → stm.inst = .call fn args →
        s'.frame.func.extern? fn = some extF → s'.frame.getMany args = .ok vals →
        vals.map (·.ty) = Clif.AbiParam.tys extF.sig.params →
        (∀ k w, ldF.fb.words[k]? = some w →
          Arm.read_mem_bytes 4 (ldF.base + BitVec.ofNat 64 (4 * k)) x = w) →
        StackAvail KB ldF.af (Link.enter ldF x) →
        (∀ a, GB a → ¬ StackBelow (frameDrop ldF.af + KB) (spv (Link.enter ldF x)) a) →
        link2.M x = Link.enter ldF x ∧ stepEvs x = [] ∧ cls x = .plain ∧
          (link2.act ldF (Link.enter ldF x) KB GB).Wf ∧
          ArgsAtEntry (link2.act ldF (Link.enter ldF x) KB GB).F fL.sig vals
            (bodyOf ldF.af (Link.enter ldF x)) := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk, -, hcu⟩ := driverA_fC henv c
  obtain ⟨L, ss, ss', H3, -⟩ := CallLayers.prep_init (vc := vcC) (vcp := RC.vc)
    CallResumeL.Witness.prepC
  obtain ⟨cc, ins, a0, hat0, -⟩ := CallLayers.alloc_init (vc := RC.vc) (rf := RC.rf) allocC ckeep
  obtain ⟨hlow, -, -, -, hind, hv, hnt, -, hout0, -, hexts⟩ := checksFC
  refine ⟨ctx, st0, R, gn, bl, A, L, ss', cc, ins, H, fun hq hP hm2 hm3 hm4 hbody hcl hext hvals
    htys hcode hstB hgB => ?_⟩
  have hB : (extF.name, ldF) ∈ link2.fns := by rw [name_extF]; simp [link2]
  obtain ⟨h1, h2, h3, h4, -, -, -, -, -, -, h5⟩ := Link.call_end ok2 (nA := "f") (FA := callerF)
    (by simp [link2]) (s0 := sC0) (K := 0) (G := GL) wf_C H hchk
    CallArgsL2.Witness.resLen_fC hcu hlow (List.isEmpty_iff.mp hind) hv hnt hout0 rfl
    (fun _ _ h => by cases h) (fun _ _ _ => rfl) H3 hat0 Concurrency.CallArgsAt.Witness.usesV_fC
    CallResumeAll.Witness.defs_fC.1 hq hP hm2 hm3 hm4 hbody hcl hext
    (fun e he _ => by rw [hexts, List.mem_singleton] at he; rw [he]) hvals htys hB static_ld
    hcode hstB hgB sig_fL
  exact ⟨h1, h2, h3, h4, h5⟩

end Concurrency.LinkedMachine.Witness
