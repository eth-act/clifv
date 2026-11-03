import FV.Backend.Proof.StockAcquireRhsReceipts
import FV.Backend.Proof.StockAcquireRootForward
import FV.Backend.Proof.StockAllocationFlow

namespace Backend.Stock.Proof.AcquireHelpers
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- Actual RHS success derives its fresh single result and the precise emitted state.
The proof obtains the sink and acquire executions internally. -/
theorem acquire_rhs_output {ctx : Ctx} {st next : State} {before after : Array RuleId}
    {env : Isle.Interp.Env V} {n producer : Nat} {ty flags out : V}
    (typeValue : env[1]? = some (some ty))
    (flagValue : env[2]? = some (some flags))
    (producerValue : env[4]? = some (some (.inst producer)))
    (run : (evalExpr program (Stock.sem ctx) {} (n+100) rule_lower_1272.rhs env).run (st,before) =
      .ok (some out,next,after)) :
    ∃ address sunk sinkTrace instruction,
      (applyTerm program (Stock.sem ctx) {} (n+93) 27 564 [.inst producer]).run
        (st,before) = .ok (some address,sunk,sinkTrace) ∧
      MInst.ofV (.data 58 42 [ty,.reg (sunk.base.fresh .int).1,address,flags]) = some instruction ∧
      out = .regsVec [[(sunk.base.fresh .int).1]] ∧
      next = {sunk with base := (sunk.base.fresh .int).2.emit instruction} ∧
      st.base.nextVreg ≤ sunk.base.nextVreg := by
  simp only [rule_lower_1272,evalExpr.eq_7,evalArgs.eq_3,evalExpr.eq_2,evalArgs.eq_2,
    typeValue,flagValue,producerValue,isel_monad] at run
  cases sinkCall : (applyTerm program (Stock.sem ctx) {} (n+93) 27 564 [.inst producer]).run
      (st,before) with
  | error message => rw [sinkCall] at run; cases run
  | ok result =>
    obtain ⟨address,sunk,sinkTrace⟩ := result
    cases address with
    | none => rw [sinkCall] at run; simp only [isel_monad] at run; cases run
    | some address =>
      rw [sinkCall] at run
      simp only [isel_monad] at run
      cases acquireCall : (applyTerm program (Stock.sem ctx) {} (n+97) 27 422 [ty,flags,address]).run
          (sunk,sinkTrace) with
      | error message => rw [acquireCall] at run; cases run
      | ok result =>
        obtain ⟨value,emitted,emitTrace⟩ := result
        cases value with
        | none => rw [acquireCall] at run; simp only [isel_monad] at run; cases run
        | some value =>
          obtain ⟨instruction,decoded,valueEq,stateEq⟩ :=
            stock_acquire_call (fuel := n+96) rfl (by omega) acquireCall
          have output := output_reg_forward data_program ctx (cfg := {}) rfl emitted emitTrace
            (n+89) (sunk.base.fresh .int).1
          rw [acquireCall] at run
          simp only [isel_monad,valueEq] at run
          rw [output] at run
          have same := Except.ok.inj run
          have outEq := Option.some.inj (congrArg Prod.fst same)
          have nextEq := congrArg (fun q => q.2.1) same
          exact ⟨address,sunk,sinkTrace,instruction,rfl,decoded,outEq.symm,
            nextEq.symm.trans stateEq,(stock_apply_allocationLe sinkCall).1⟩

end Backend.Stock.Proof.AcquireHelpers
