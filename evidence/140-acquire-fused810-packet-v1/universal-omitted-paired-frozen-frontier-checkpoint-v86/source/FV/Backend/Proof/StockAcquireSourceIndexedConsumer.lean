import FV.Backend.Proof.StockAcquireTrappedPrefixValues

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual indexed consumer step supplies its successful extension value. -/
theorem source_uextend_result_value {ctx : Ctx} {inst value : Nat} {info : IInfo} {ty : Clif.Ty}
    {env : Clif.Env} {program : Clif.Program} {before after : Clif.Frame × Clif.Mem}
    (installed : ctx.insts[inst]? = some info) (source : info.clif = some (.extend .uextend ty value))
    (step : SourceInstResult env program ctx inst before after) :
    ∃ widened,Clif.evalInst before.1 before.2 (.extend .uextend ty value) = .ok ([widened],after.2) := by
  obtain ⟨actual,original,values,regs,rest,found,clif,body,evaluated,updated,frame⟩ := step
  have infoEq := Option.some.inj (found.symm.trans installed)
  subst actual
  have instEq := Option.some.inj (clif.symm.trans source)
  subst original
  change Clif.evalInst before.1 before.2 (.extend .uextend ty value) = .ok (values,after.2) at evaluated
  obtain ⟨input,found,width,results,memory⟩ := evalInst_uextend_ok evaluated
  exact ⟨⟨ty,Clif.Sem.uextend ty.width input.bits⟩,by rw [← results];exact evaluated⟩

end Backend.Stock.Proof.Acquire810
