import FV.Backend.Proof.StockAcquireEntry

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

private theorem frame_equal {a b : Clif.Frame} (function : a.func = b.func) (registers : a.regs = b.regs)
    (slots : a.slots = b.slots) (body : a.body = b.body) (term : a.term = b.term) : a = b := by
  cases a
  cases b
  simp_all

/-- The existing source entry derives the exact original argument and frame internally. -/
theorem original_entry_normal_form {args : List Clif.Val} {state : Clif.State}
    (entered : ClifEntry function args state) :
    ∃ pointer : BitVec 64,args = [⟨.i64,pointer⟩] ∧ state.frame = entry pointer ∧ state.callers = [] := by
  have signature := entered.sig
  cases args with
  | nil => simp [function] at signature
  | cons arg rest =>
    cases rest with
    | cons other rest => simp [function] at signature
    | nil =>
      obtain ⟨ty,bits⟩ := arg
      have type : ty = .i64 := by simpa [function] using (List.cons.inj signature).1
      subst ty
      obtain ⟨block,present,body,term,types,registers⟩ := entered.entry
      have sameBlock : block = function.blocks[0]! := by
        simpa [Clif.Function.entry?,function] using present.symm
      subst block
      have sameRegisters : (entry bits).regs = state.frame.regs := Option.some.inj registers
      have sameSlots : state.frame.slots = [] := by simpa [function] using entered.slotIds
      refine ⟨bits,rfl,?_,entered.callers⟩
      exact frame_equal entered.func sameRegisters.symm sameSlots body term

end Backend.Stock.Proof.Acquire810
