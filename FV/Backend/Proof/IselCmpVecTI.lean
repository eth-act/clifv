module

public import FV.Backend.Proof.IselCmpVec
public import FV.Backend.Proof.IselBaseTI

@[expose] public section

/-!
# `IselCmpVec` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselCmpVec`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
set_option maxHeartbeats 4000000 in
include hp hc in
/-- The result type of a binary instruction of E has no `vector_size`. -/
theorem vector_size_binary_absurdTI {f : Clif.Function} (hctx : CtxInvT f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hic : info.clif = some inst) {cop : Clif.BinaryOp} {nm : String} {ko : Nat} {w3 : V}
    (hname : (variantNames 151)[ko]? = some nm) (hcop : binaryOpcode cop = some nm)
    (hdd : V.data 152 2 [V.data 151 ko [], w3] = info.data) {n : Nat} (hn : 60 ≤ n)
    {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 97 310 [.ty (info.resTys.head?.getD .invalid)] s v s') :
    False := by
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, x, y, rfl, hety, -⟩ := instData_binary_inv hname hcop hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at h
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety)] at h
  exact vector_size_scalar hp hc hn (cmp_eTy_widths hety) h

end
section Root
variable {p : Program} (hp : Data p)
set_option maxHeartbeats 8000000 in
include hp in
theorem vec_smin_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1233 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = info.data) := ⟨‹_›⟩
  obtain ⟨h310⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 97 310 _ _ _ _) := ⟨‹_›⟩
  exact (vector_size_binary_absurdTI hp hco hctx hi hic (cop := .smin) rfl rfl hdd (by omega) h310).elim

set_option maxHeartbeats 8000000 in
include hp in
theorem vec_umin_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1239 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = info.data) := ⟨‹_›⟩
  obtain ⟨h310⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 97 310 _ _ _ _) := ⟨‹_›⟩
  exact (vector_size_binary_absurdTI hp hco hctx hi hic (cop := .umin) rfl rfl hdd (by omega) h310).elim

set_option maxHeartbeats 8000000 in
include hp in
theorem vec_smax_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1245 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = info.data) := ⟨‹_›⟩
  obtain ⟨h310⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 97 310 _ _ _ _) := ⟨‹_›⟩
  exact (vector_size_binary_absurdTI hp hco hctx hi hic (cop := .smax) rfl rfl hdd (by omega) h310).elim

set_option maxHeartbeats 8000000 in
include hp in
theorem vec_umax_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1251 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  obtain ⟨hins⟩ : Nonempty (ctx.insts[ii]? = some _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  obtain ⟨hdd⟩ : Nonempty (V.data 152 2 _ = info.data) := ⟨‹_›⟩
  obtain ⟨h310⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 97 310 _ _ _ _) := ⟨‹_›⟩
  exact (vector_size_binary_absurdTI hp hco hctx hi hic (cop := .umax) rfl rfl hdd (by omega) h310).elim

end Root
end Backend.Proof
