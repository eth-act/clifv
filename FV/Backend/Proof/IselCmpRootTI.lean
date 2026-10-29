module

public import FV.Backend.Proof.IselCmpRoot
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselFamALUATI

@[expose] public section

/-!
# `IselCmpRoot` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselCmpRoot`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
end
section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
end
section Root
variable {p : Program} (hp : Data p)
set_option maxHeartbeats 8000000 in
include hp in
theorem icmp_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2215 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h652
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨cc, ty, x, y, rfl, rfl, rfl⟩ := instData_icmp_inv hdat
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  obtain ⟨h715⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 715 _ _ _ _) := ⟨‹_›⟩
  have hE := emit_icmp_okT hp hco hR hctx (hxi := by int_posA) (hyi := by int_posA) (hn := by omega) hvb h652
  obtain ⟨m0, cond, hflag, rfl, hst⟩ := lcrb_ok hp hco (hn := by omega) hE.shape h715
  isel_call hp hco [cmp_output_reg_ok]
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_lcrb hR hE hflag
  rw [hst]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ w vals cm' _ hh hdf ho
  obtain ⟨a, b, hx, hy, rfl, rfl⟩ := evalInst_icmp_ok ho
  obtain ⟨hu, hr⟩ := hsem fr ρ _ hh hdf ⟨ty, a, b, getAs_ok hx, getAs_ok hy, rfl⟩
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr w).imp fun ρ' _ _ h => by
    rw [h]; exact vholds_bool8 _⟩

set_option maxHeartbeats 8000000 in
include hp in
theorem uextend_icmp_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1281 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h652 hres
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, z, rfl, hety, rfl⟩ := instData_uextend_inv hdat
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  rename_i hj _ hi2 hd2
  obtain ⟨cl, hcl, hdat2⟩ := ctxInv_clifTI hctx hj hi2
  rw [← hd2] at hdat2
  obtain ⟨cc, ty', x, y, rfl, rfl, rfl⟩ := instData_icmp_inv hdat2
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  obtain ⟨h652⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 652 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h715⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 715 _ _ _ _) := ⟨‹_›⟩
  have hE := emit_icmp_okT hp hco hR hctx (hxi := by int_posA) (hyi := by int_posA) (hn := by omega) hvb h652
  obtain ⟨m0, cond, hflag, rfl, hst⟩ := lcrb_ok hp hco (hn := by omega) hE.shape h715
  isel_call hp hco [cmp_output_reg_ok]
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_lcrb hR hE hflag
  rw [hst]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ w vals cm' _ hh hdf ho
  obtain ⟨v, hzv, -, rfl, rfl⟩ := evalInst_uextend_ok ho
  obtain ⟨vals2, hev, hl⟩ := hdf.1 z _ _ _ v hj hi2 hcl rfl hzv
  obtain ⟨a, b, hx, hy, rfl, -⟩ := evalInst_icmp_ok (hev default)
  have hv := lookup_zip_single hl
  subst hv
  obtain ⟨hu, hr⟩ := hsem fr ρ _ hh hdf ⟨ty', a, b, getAs_ok hx, getAs_ok hy, rfl⟩
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr w).imp fun ρ' _ _ h => by
    rw [h]; exact vholds_uextend_bool8 hety _⟩

end Root
end Backend.Proof
