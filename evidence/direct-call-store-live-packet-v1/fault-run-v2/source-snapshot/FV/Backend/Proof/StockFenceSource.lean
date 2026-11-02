import FV.Backend.Proof.StockProtectedSinkDriver

namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- Original mapped fence data excludes the sinking formats at this slot alone. -/
theorem fence_no_load_at {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {slot : Nat} {info : IInfo} (found : ctx.insts[slot]? = some info)
    (original : info.clif = some .fence) : NoLoadAt ctx slot := by
  intro actual lookup fmt fields load
  have same : actual = info := Option.some.inj (lookup.symm.trans found)
  subst actual
  apply inst_data_no_load (mapped.instE slot info _ found original) ?_
    (mapped.data slot info _ found original) fmt fields load
  simp [CastComplete.MemoryFormat,instNames]

/-- The original result-type mapping derives the fence's empty result list. -/
theorem fence_results_empty {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {slot : Nat} {info : IInfo} (found : ctx.insts[slot]? = some info)
    (original : info.clif = some .fence) :
    ctx.insts[slot]!.results = [] := by
  obtain ⟨tys,typed,_,length⟩ := mapped.resTys slot info _ found original
  change some [] = some tys at typed
  cases typed
  have empty : info.results = [] := List.eq_nil_of_length_eq_zero length
  simpa only [getElem!_def,found,Option.getD_some] using empty


end Backend.Stock.Proof.SinkRules
