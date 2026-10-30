import FV.Concurrency.CallResumeAll
import FV.Concurrency.IselCallWitness
import FV.Concurrency.CallEntryWitness

/-!
# Witness: the caller resumed at every layer (#473, step (3))

**`resume_all_fC`**: `CallResumeAll.resume_all` for the compiled caller of `atomic_load`
(`CallSeg.WitnessC.RC`, `fC`), every static premise discharged: the driver's relations
(`driverC`), `prepare`'s and the checker's (`CallLayers.prep_init`, `alloc_init`), the
function's checks (`checksFC`), its one call's def `x0` (virtual), the callee's `rets` register
`x0` (as the compiled `atomic_load` returns, `instL2`), one return value of `ld`'s signature.
The pause and the callee's return stay premises (`CallRetsN.Witness.arm_entryCRN_fC` reaches
such pauses).

Checks by `native_decide` (witness only).
-/

namespace Concurrency.CallResumeAll.Witness

open Arm ArmThread ClifThread Backend Backend.Proof Backend.Proof.Driver VCodeThread PrepThread
  AllocThread ArmAllocThread IselThread ThreadRefine E2E RealizeCompiled.Witness
  IselRefines.Witness CallSeg.WitnessC IselCall IselCall.Witness CallEntry.Witness IselCallRet

/-- The calls of the caller: one def, `x0`, virtual (as a check). -/
def callsB : Bool :=
  vcpC.blocks.all fun vb => vb.insts.all fun i => match i with
    | .call info => info.defs.map (·.1) == [.x 0] &&
        info.defs.all (fun d => match d.2 with | .vreg _ _ => true | _ => false)
    | _ => true

theorem checksR : callsB = true ∧ (sigRets extF.sig).length = 1 := by native_decide

theorem calls_fC {b k : Nat} {vb : VBlock} {info : CallInfo} (hb : RC.vc.blocks[b]? = some vb)
    (hk : vb.insts[k]? = some (.call info)) :
    info.defs.map (·.1) = [.x 0] ∧
      ∀ d ∈ info.defs, ∃ (n : Nat) (c : RegClass), d.2 = .vreg n c := by
  have h := checksR.1
  simp only [callsB, Array.all_eq_true] at h
  change vcpC.blocks[b]? = some vb at hb
  obtain ⟨hb1, rfl⟩ := Array.getElem?_eq_some_iff.mp hb
  obtain ⟨hk1, e⟩ := Array.getElem?_eq_some_iff.mp hk
  have h2 := h b hb1 k hk1
  rw [e] at h2
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h2
  refine ⟨h2.1, fun d hd => ?_⟩
  have := h2.2 d hd
  split at this
  · exact ⟨_, _, by assumption⟩
  · cases this

/-- **The caller of `atomic_load` resumed at every layer** (module doc). -/
theorem resume_all_fC {env : Clif.Env} (henv : env.extern "ld" = none) (c : BitVec 64) :
    ∃ (ctx : Ctx) (st0 : LState) (R : Reg → Reg) (gn : Nat → Nat) (bl : List BLow)
      (A : Nat → Nat → List Clif.ValueId) (L : Nat → Prop) (ss' : Array (Array Nat))
      (cc : CheckCtx) (ins : Array (Option AState)),
      DriverHypT fC vcC ctx st0 R gn bl A (csem RC.F RC.ctx RC.X) (RelW ΓC fC c) env pCL ∧
      ∀ {RB : RL} {r₀ : Reg → CV} {x : ArmState} {s' : Clif.State} {vV' vP' : VState CV ArmState}
        {cM' : MState CV ArmState} {slots : List (Clif.SlotId × Nat)} {ra : BitVec 64}
        {r₀B : Reg → CV} {y : ArmState} {ysB : List CV} {rvals : List Clif.Val}
        {FB : BitVec 64 → Prop} {cmB : Clif.Mem} {wB : ArmState} {bases : List Nat}
        {stm : Clif.Stmt} {rest : List Clif.Stmt} {fn : Clif.FnRef} {args : List Clif.ValueId}
        {vals : List Clif.Val} {regs' : Clif.Regs},
        RB.Wf → Q RC x (.run cM') → AInv RC (.run cM') → Pause RC (.run cM') → AtCallS s' →
        Match fC ctx R gn bl A (RelW ΓC fC c) slots s' vV' →
        PMatch vcC RC.vc (csem RC.F RC.ctx RC.X) (cEvs RC.F RC.ctx) L ss' (.run vV') (.run vP') →
        MatchRun cc ins ckeep r₀ cM' vP' →
        AbiCall RB.fb RB.base ra RB.s0 → RetC RB ra r₀B y →
        (∀ f, f ≠ .PC → f ≠ .GPR 30#5 → Arm.r f RB.s0 = Arm.r f x) →
        xreg 30 RB.s0 = Arm.r .PC x + 4#64 → (∀ a, RC.FK a → RB.s0.mem a = x.mem a) →
        (∀ a, RC.FK a → RB.G a) →
        (∀ r ∈ calleeSaved, ckeep r (r₀B r) = ckeep r
          (locVal RB.fr (iterN RB.step (prologueLines RB.af.saves RB.af.frameSize).length RB.s0) (.reg r))) →
        y.program = x.program →
        (∀ (j : Nat) (v q : Reg) (u : CV), [(Reg.vreg 2 .int, Reg.x 0)][j]? = some (v, q) →
          ysB[j]? = some u → regVal y q = u) →
        PrefixHold rvals ysB → rvals.length ≤ 1 → MemRel FB ΓC.syms cmB wB →
        (∀ a n, ((cmB.free bases).leave).valid a n = true → s'.mem.valid a n = true) →
        (∀ a, ¬ FB a → y.mem a = wB.mem a) →
        s'.frame.body = stm :: rest → stm.inst = .call fn args →
        s'.frame.func.extern? fn = some extF → s'.frame.getMany args = .ok vals →
        vals.map (·.ty) = Clif.AbiParam.tys extF.sig.params →
        rvals.map (·.ty) = Clif.AbiParam.tys extF.sig.returns →
        s'.frame.regs.setMany stm.results rvals = some regs' →
        ∃ vV'' vP'' cM'',
          Match fC ctx R gn bl A (RelW ΓC fC c) slots { s' with
              frame := { s'.frame with regs := regs', body := rest },
              mem := (cmB.free bases).leave } vV'' ∧
          PMatch vcC RC.vc (csem RC.F RC.ctx RC.X) (cEvs RC.F RC.ctx) L ss' (.run vV'')
            (.run vP'') ∧
          MatchRun cc ins ckeep r₀ cM'' vP'' ∧ Q RC y (.run cM'') ∧ AInv RC (.run cM'') := by
  obtain ⟨ctx, st0, R, gn, bl, A, H, hchk⟩ := driverC henv c
  obtain ⟨L, ss, ss', H3, -⟩ := CallLayers.prep_init (vc := vcC) (vcp := RC.vc)
    CallResumeL.Witness.prepC
  obtain ⟨cc, ins, a0, hat0, -⟩ := CallLayers.alloc_init (vc := RC.vc) (rf := RC.rf) allocC ckeep
  obtain ⟨hlow, -, -, -, hind, hv, hnt, -, hout0, -, hexts⟩ := checksFC
  refine ⟨ctx, st0, R, gn, bl, A, L, ss', cc, ins, H, fun hRB hq hA hP hat hm2 hm3 hm4 hent hy
    hfx hlr hm0 hG hr₀B hprog hus hpreB hlenR hB hval hmemB hbody hcl hext hvals htys hrty
    hregs => ?_⟩
  refine resume_all wfRC hRB rfl (fun _ _ _ => rfl) H hchk hlow (List.isEmpty_iff.mp hind) hv
    hnt hout0 rfl rfl (fun _ _ h => by cases h) H3 hat0
    (fun _ _ _ _ hb hk => (calls_fC hb hk).2) hq hA hP hat hm2 hm3 hm4 hent hy hfx hlr hm0 hG
    hr₀B hprog hus hpreB hB hval hmemB hbody hcl hext ?_ hvals htys hrty hregs ?_
  · intro e he _
    rw [hexts, List.mem_singleton] at he
    rw [he]
  · intro _ _ _ info hb hk
    have hd := (calls_fC hb hk).1
    obtain ⟨d, hd0⟩ : ∃ d, info.defs = [d] := by
      cases h : info.defs with
      | nil => rw [h] at hd; simp at hd
      | cons d ds =>
        cases ds with
        | nil => exact ⟨d, rfl⟩
        | cons _ _ => rw [h] at hd; simp at hd
    rw [hd0] at hd
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hd
    refine ⟨fun j d' hj => ?_, by rw [hd0]; exact hlenR, by rw [hd0, checksR.2]; rfl⟩
    rw [hd0] at hj
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      exact ⟨_, by rw [hd]; rfl⟩
    | succ j => simp at hj

end Concurrency.CallResumeAll.Witness
