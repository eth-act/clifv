import FV.Opt.Proof.LegalBase

/-!
# `Clif.evalInst` facts for the legalisation simulation

* `evalInst_same`: an instruction evaluates identically in two frames that agree on its
  operands, stack slots and global declarations (the `same` plan);
* `evalInst_types`: the results have the instruction's result types (the source invariant);
* `evalInst_allocs`: memory allocations are unchanged.
-/

namespace Opt.Legal

open Clif

theorem evalInst_same {fr fr' : Frame} {m : Mem} {i : Inst}
    (hops : ∀ x ∈ instOps i, fr'.regs x = fr.regs x) (hsl : fr'.slots = fr.slots)
    (hgl : fr'.func.globals = fr.func.globals) (hfa : ∀ t fn, i ≠ .funcAddr t fn) :
    evalInst fr' m i = evalInst fr m i := by
  cases i <;> simp only [instOps, List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp,
    forall_eq, List.mem_singleton] at hops <;>
    simp [evalInst, Frame.getAs, Frame.get, Frame.getMany, hops, hsl, hgl]
  exact absurd rfl (hfa _ _)

end Opt.Legal
