import FV.Backend.Proof.IselMemRoots
import FV.Backend.Proof.LowerContractT

/-!
# Integer memory roots over typed contexts: common facts (S11e5 Stage C, slice 7)

`CtxInv.resTysE` (every result type an E type) holds in a typed context at its subset-E
instructions (`CtxT.resTysE`: integer externs, a `call_indirect`'s integer signature).
`mem_rootTI` is `mem_root` over `CtxT` (with `hctxT : CtxT f ctx` and `hE : instE inst` in the
context).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- **The result types of a subset-E instruction of a typed context are E's.** -/
theorem CtxT.resTysE {f : Clif.Function} {ctx : Ctx} (h : CtxT f ctx) {ii : Nat} {info : IInfo}
    {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hE : Compile.instE inst = true) : ∀ t ∈ info.resTys, t ∈ eCTys := by
  intro t ht
  have hm := h.inv.resTysM ii info hi t ht
  obtain ⟨tys, htys, hres, -⟩ := h.inv.resTys ii info inst hi hc
  rw [hres] at ht
  obtain ⟨ty, hty, rfl⟩ := List.mem_map.mp ht
  have hnf : ty.isFloat = false := by
    cases hci : Compile.isCallIndirect inst
    · exact resTy_not_float_calls (h.calls.at hi hc) hE hci ty (by rw [htys]; exact hty)
    · cases inst with
      | callIndirect sig cl args =>
        cases hl : f.sigDecls.lookup sig with
        | none => simp [Clif.Inst.resultTypes, hl] at htys
        | some sg =>
          simp only [Clif.Inst.resultTypes, hl, Option.map_some, Option.some.injEq] at htys
          subst htys
          obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hty
          have := List.all_eq_true.mp
            (sigIntB_iff.mp (instData_callIndirect_int (h.inv.data ii info _ hi hc) hl)).2 q hq
          revert this; cases q.ty <;> decide
      | _ => simp [Compile.isCallIndirect] at hci
  revert hm hnf
  cases ty <;> simp [mCTys, eCTys, CTy.ofClif, Clif.Ty.isFloat]

/-- The operands of a subset-E `store` are both in integer positions. -/
theorem intArgs_store_E {op : Clif.StoreOp} {ty : Clif.Ty} {fl : Clif.MemFlags} {x q : Nat}
    {off : Int} (hE : Compile.instE (.store op ty fl x q off) = true) :
    intArgs (.store op ty fl x q off) = [x, q] := by
  have hf : ty.isFloat = false := by
    revert hE; cases ty <;> simp [Compile.instE, Compile.tyE, Clif.Ty.isFloat, Clif.Ty.isInt]
  show (if ty.isFloat then [q] else [x, q]) = _
  rw [hf]; rfl

/-- `mem_rootTI hctx hi hic`: `mem_root` over a typed context (`hctxT : CtxT f ctx`,
`hE : Compile.instE inst = true`). -/
macro "mem_rootTI " hctx:ident hi:ident hic:ident : tactic => `(tactic| (
  have hdat0 := CtxInvT.data $hctx _ _ _ $hi $hic
  have $(Lean.mkIdent `hA64) := fun x => CtxInvT.addr64 $hctx _ _ _ x $hi $hic
  have hRT := CtxInvT.resTys $hctx _ _ _ $hi $hic
  have $(Lean.mkIdent `hRE) := CtxT.resTysE $(Lean.mkIdent `hctxT) $hi $hic $(Lean.mkIdent `hE)
  simp only [$hi:ident, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hdat := data_trans hdat0 ‹_›
  first
    | have := inv_load_root hdat
    | have := inv_store_root hdat
    | have := inv_symbolValue_root hdat
    | have := inv_stackAddr hdat
  isel_destruct; subst_vars
  try rw [intArgs_store_E $(Lean.mkIdent `hE)] at $(Lean.mkIdent `hops):ident
  try simp only [intArgs, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at $(Lean.mkIdent `hops):ident
  try obtain ⟨_, _⟩ := $(Lean.mkIdent `hops)
  repeat (mem_inv_simp [] at * <;> isel_destruct <;> subst_vars)))

end Backend.Proof
