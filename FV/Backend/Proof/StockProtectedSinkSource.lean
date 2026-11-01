import FV.Backend.Proof.StockProtectedSinkFrame
import FV.Backend.Proof.StockNoLoadSource

namespace Backend.Stock.Proof.SinkRules
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program

/-- Original mapped store data excludes the sinking formats at this slot alone. -/
theorem store_no_load_at {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {slot : Nat} {info : IInfo} {op : Clif.StoreOp} {ty : Clif.Ty}
    {flags : Clif.MemFlags} {value pointer : Nat} {offset : Int}
    (found : ctx.insts[slot]? = some info)
    (original : info.clif = some (.store op ty flags value pointer offset)) : NoLoadAt ctx slot := by
  intro actual lookup fmt fields load
  have same : actual = info := Option.some.inj (lookup.symm.trans found)
  subst actual
  apply inst_data_no_load (mapped.instE slot info _ found original) ?_
    (mapped.data slot info _ found original) fmt fields load
  simp [CastComplete.MemoryFormat,instNames]

/-- The original result-type mapping derives the store's empty result list. -/
theorem store_results_empty {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {slot : Nat} {info : IInfo} {op : Clif.StoreOp} {ty : Clif.Ty}
    {flags : Clif.MemFlags} {value pointer : Nat} {offset : Int}
    (found : ctx.insts[slot]? = some info)
    (original : info.clif = some (.store op ty flags value pointer offset)) :
    ctx.insts[slot]!.results = [] := by
  obtain ⟨tys,typed,_,length⟩ := mapped.resTys slot info _ found original
  change some [] = some tys at typed
  cases typed
  have empty : info.results = [] := List.eq_nil_of_length_eq_zero length
  simpa only [getElem!_def,found,Option.getD_some] using empty

/-- Filling any actual terminator preserves a different protected source slot. -/
theorem no_load_at_term_ctx {ctx : Ctx} {slot ti : Nat} (safe : NoLoadAt ctx slot)
    (different : slot ≠ ti) (data : V) : NoLoadAt (termCtx ctx ti data) slot := by
  intro info found fmt fields load decoded
  rw [termCtx_insts_ne different] at found
  exact safe info found fmt fields load decoded

/-- Exception-register reservations preserve the original mapping facts. -/
theorem mapped_with_try_regs {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    (regs : List Reg × List Reg) : MappedCtxInv f {ctx with tryRegs := regs} := by
  exact {mapped with}

/-- Exception-register reservations preserve the protected source data. -/
theorem no_load_at_with_try_regs {ctx : Ctx} {slot : Nat} (safe : NoLoadAt ctx slot)
    (regs : List Reg × List Reg) : NoLoadAt {ctx with tryRegs := regs} slot := safe

end Backend.Stock.Proof.SinkRules
