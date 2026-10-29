module

public import FV.Backend.Proof.IselFamALUA
public import FV.Backend.Proof.IselBaseTI

@[expose] public section

/-!
# `IselFamALUA` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamALUA`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
section Inversion
variable {p : Program} (hp : Data p) (ctx : Ctx)
end Inversion
section Clif
/-- The instruction behind a matched data value (`CtxInv.data` needs `info.clif`; for a
value's definition `CtxInv.defClif` supplies it). -/
theorem ctxInv_clifTI {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {y j : Nat}
    {info : IInfo} (hj : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info) :
    ∃ cl, info.clif = some cl ∧ instData f cl = .ok info.data := by
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp (hctx.defClif y j info hj hi)
  exact ⟨cl, hcl, hctx.data j info cl hi hcl⟩

end Clif
section Root
variable {p : Program} (hp : Data p)
include hp in
/-- **Step 1 for a `Binary (O) (x y)` root rule**: the matched instruction is `cop ty x y`
(`O` the opcode of `cop`), with its data and result type, and the value-pair pattern matched
`[x, y]`. -/
theorem binary_root_invTI {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    {cfg : Config} {m : Nat} {r : Rule} {s s1 : LState × Array RuleId} {env : Interp.Env V}
    {tyPat : Pattern} {opT : TermId} {rest : List Pattern} {to : Term} {ko : Nat}
    {cop : Clif.BinaryOp} {n : String}
    (hargs : r.args = [.term 18 209 [tyPat, .term 152 2449 (.term 151 opT [] :: rest)]])
    (hto : termOf p opT = .ok to) (hko : to.kind = .enumVariant ko)
    (hname : (variantNames 151)[ko]? = some n) (hcop : binaryOpcode cop = some n)
    (h : (matchRule p (sem ctx) cfg (m + 1) r [.inst ii]).run s = .ok (some env, s1)) :
    ∃ ty x y e0 e1, inst = .binary cop ty x y ∧
      info.data = .data 152 2 [.data 151 ko [], .values [x, y]] ∧
      info.resTys.head? = some (.int ty.width) ∧ ty.width ≤ 64 ∧
      matchArgs p (sem ctx) s.1 rest [.values [x, y]] e0 = .ok (some e1) ∧
      (matchIfLets p (sem ctx) cfg m r.iflets e1).run s = .ok (some env, s1) := by
  obtain ⟨info', fs, e0, e1, hi', hd, hrest, hil⟩ :=
    root_match_inv hp ctx hargs hp.t2449 term_2449_kind hto hko h
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hc
  rw [hd] at hdat
  obtain ⟨ty, x, y, rfl, hety, rfl⟩ := instData_binary_inv hname hcop hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  refine ⟨ty, x, y, e0, e1, rfl, hd, ?_, eTy_width hety, hrest, hil⟩
  rw [hres]; simp [ofClif_int_width (isInt_of_eTy hety)]

end Root
section Code
end Code
section Forms
end Forms
section Inversion2
variable {p : Program} (hp : Data p) (ctx : Ctx)
end Inversion2
section One
end One
section IfLet
variable {p : Program} (hp : Data p) (ctx : Ctx)
include hp in
/-- **`imm12_from_negated_value` succeeded on `y`**: `y` is defined by an `iconst`. -/
theorem negated_value_invTI {f : Clif.Function} (hctx : CtxInvT f ctx) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m : Nat} {y : Nat} {s s2 : LState × Array RuleId} {v : V}
    (h : (applyTerm p (sem ctx) cfg (m + 5) 64 344 [.value y]).run s = .ok (some v, s2)) :
    ∃ j infoj ty c, ctx.defInst? y = some j ∧ ctx.insts[j]? = some infoj ∧
      infoj.clif = some (.iconst ty c) ∧
      infoj.data = .data 152 35 [.data 151 57 [], .int (imm64OfIconst ty c)] ∧
      infoj.resTys.head? = some (.int ty.width) := by
  obtain ⟨r, hr, m0, env0, s1, st, tr, hmn, hmatch, -, -⟩ :=
    applyTerm_internal_some hc hp.t344 term_344_kind rfl h
  rw [hp.r344, List.mem_singleton] at hr
  rw [hp.r344, List.length_singleton] at hmn
  subst hr
  obtain ⟨m1, rfl⟩ : ∃ m1, m0 = m1 + 1 := ⟨m0 - 1, by omega⟩
  obtain ⟨env1, ha, -⟩ := matchRule_some_inv hmatch
  obtain ⟨e1, hp1, -⟩ := matchArgs_cons_inv (qs := []) ha
  obtain ⟨j, infoj, fs, e0, hj, hij, hdj, -⟩ :=
    defInst_match_inv hp ctx hp.t2482 term_2482_kind hp.t2341 term_2341_kind hp1
  obtain ⟨cl, hcl, hdat⟩ := ctxInv_clifTI hctx hj hij
  rw [hdj] at hdat
  obtain ⟨ty, c, rfl, rfl⟩ := instData_iconst_inv hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys j infoj _ hij hcl
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hE := instData_iconst_eTy hdat
  exact ⟨j, infoj, ty, c, hj, hij, hcl, hdj, by
    rw [hres]; simp [ofClif_int_width (isInt_of_eTy hE)]⟩

end IfLet
section Rhs
variable {p : Program} {σ : Type} {sem' : Isle.Sem V σ} {cfg : Config}
end Rhs
section Forms2
end Forms2
end Backend.Proof
