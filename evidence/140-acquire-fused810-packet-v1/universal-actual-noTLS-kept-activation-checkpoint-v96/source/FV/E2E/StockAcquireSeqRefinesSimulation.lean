import FV.E2E.Pair
import FV.E2E.Lockstep

namespace E2E.StockAcquirePending
open Backend Backend.Proof
set_option autoImplicit false
set_option Elab.async false

/-- A local semantic simulation preserves complete successful straight-line execution.
Both runs keep the exact same virtual register file. -/
theorem seqRun_fall_simulation {W0 W1 : Type} {model : ISem CV W0} {actual : ISem CV W1}
    {R : W1 → W0 → Prop} (code : List MInst)
    (step : ∀ inst ∈ code,∀ uses before actualBefore outs after ctl,
      R actualBefore before → model inst uses before = some (outs,after,ctl) →
      ∃ actualAfter,actual inst uses actualBefore = some (outs,actualAfter,ctl) ∧ R actualAfter after) :
    ∀ regs before nextRegs after,
      seqRun model code regs before = some (.fall nextRegs after) →
      ∀ actualBefore,R actualBefore before →
      ∃ actualAfter,seqRun actual code regs actualBefore = some (.fall nextRegs actualAfter) ∧ R actualAfter after := by
  induction code with
  | nil =>
    intro regs before nextRegs after run actualBefore related
    simp only [seqRun,Option.some.injEq,SeqEnd.fall.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    exact ⟨actualBefore,rfl,related⟩
  | cons inst rest ih =>
    intro regs before nextRegs after run actualBefore related
    cases operands : inst.operands with
    | error error => simp only [seqRun,operands] at run;cases run
    | ok ops =>
      cases modelStep : model inst (vuses ops regs) before with
      | none => simp only [seqRun,operands,modelStep] at run;cases run
      | some result =>
        obtain ⟨outs,middle,ctl⟩ := result
        by_cases length : outs.length = (ops.toList.filter Operand.isDef).length
        · cases ctl <;> simp only [seqRun,operands,modelStep,length,ite_true,
            Option.some.injEq,reduceCtorEq] at run
          obtain ⟨finish,tailRun,endEq⟩ := Option.map_eq_some_iff.mp run
          cases finish with
          | stop => cases endEq
          | fall finalRegs finalWorld =>
            cases endEq
            obtain ⟨actualMiddle,actualStep,middleRel⟩ := step inst (List.mem_cons_self ..)
              (vuses ops regs) before actualBefore outs middle .next related modelStep
            obtain ⟨actualAfter,tailActual,afterRel⟩ := ih
              (fun next member => step next (List.mem_cons_of_mem _ member))
              (vdefUpd ops outs regs) middle nextRegs after tailRun actualMiddle middleRel
            refine ⟨actualAfter,?_,afterRel⟩
            simp only [seqRun,operands,actualStep,length,ite_true,tailActual,Option.map_some]
            rfl
        · simp only [seqRun,operands,modelStep,length,ite_false] at run
          cases run

end E2E.StockAcquirePending
