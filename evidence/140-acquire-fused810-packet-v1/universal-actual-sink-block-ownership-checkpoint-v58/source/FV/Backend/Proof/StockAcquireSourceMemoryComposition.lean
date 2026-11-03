import FV.Backend.Proof.StockAcquireScanColorGap
import FV.Backend.Proof.StockOmission

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Original uncolored instructions preserve source memory under the existing omission contract. -/
theorem uncolored_source_read_frame {ctx : Ctx} {slot : Nat} {info : IInfo} {inst : Clif.Inst}
    (installed : ctx.insts[slot]? = some info) (source : info.clif = some inst)
    (quiet : Stock.colored inst = false) : SourceReadFrame ctx slot := by
  have mandatory : Stock.mustLower inst = false := by
    unfold Stock.colored at quiet
    exact (Bool.or_eq_false_iff.mp quiet).1
  intro env p before after executed
  obtain ⟨actualInfo,actual,values,regs,rest,found,original,body,evaluated,updated,frame⟩ := executed
  have infoEq := Option.some.inj (found.symm.trans installed)
  subst actualInfo
  have instEq := Option.some.inj (original.symm.trans source)
  subst actual
  exact (mustLower_outcome_quiet mandatory).1 values after.2 evaluated

/-- Successful source execution composes actual read frames without assuming memory validity or fault absence. -/
theorem source_steps_read_memory {env : Clif.Env} {p : Clif.Program} {ctx : Ctx}
    {indices : List Nat} {before after : Clif.Frame × Clif.Mem}
    (steps : SourceSteps (SourceInstResult env p ctx) indices before after)
    (reads : ∀ slot ∈ indices,SourceReadFrame ctx slot) : after.2 = before.2 := by
  revert reads
  induction steps with
  | nil state => intro reads; rfl
  | cons head tail ih =>
    intro reads
    have first := reads _ (List.mem_cons_self ..) env p _ _ head
    have rest := ih (fun slot member => reads slot (List.mem_cons_of_mem _ member))
    exact rest.trans first

end Backend.Stock.Proof.Acquire810
