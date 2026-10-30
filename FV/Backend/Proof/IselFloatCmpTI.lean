import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselFamALUATI

/-!
# `IselFloatCmp` over typed contexts (S11f)

The `CtxInvT` proofs of `IselFloatCmp`, restated over typed contexts (`CtxT`,
`LowerRuleOkTI`): `fcmp` needs no integer-position premise — its operands are float registers.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

section Root

variable {p : Program} (hp : Data p)

set_option maxHeartbeats 8000000 in
include hp in
/-- **`fcmp` of `f32`/`f64`** (`rule_lower_2176`) over typed contexts. -/
theorem fcmp_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2176 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h655
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨cc, ty, x, y, rfl, -, hok, hd2⟩ := instData_fcmp_inv hdat
  simp only [List.cons.injEq] at hd2
  obtain ⟨hv7, hvcc⟩ := hd2
  subst hv7
  obtain ⟨hvcc, -⟩ := hvcc
  subst hvcc
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  obtain ⟨h655⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 655 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h715⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 715 _ _ _ _) := ⟨‹_›⟩
  have hEc := emit_fcmp_okT (F := F) (isem := isem) hp hco hctx (hn := by omega) hok hvb h655
  obtain ⟨m0, cond, hflag, rfl, hst⟩ := lcrb_ok hp hco (hn := by omega) hEc.shape h715
  isel_call hp hco [cmp_output_reg_ok]
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_lcrb hR hEc hflag
  rw [hst]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ w vals cm' _ hh hdf ho
  obtain ⟨t, hv, hcm, hT⟩ := evalInst_fcmp_ok ho
  subst hcm
  subst hv
  obtain ⟨hu, hr⟩ := hsem fr ρ t hh hdf hT
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr w).imp fun ρ' _ _ h => by
    rw [h]; exact vholds_bool8 _⟩

set_option maxHeartbeats 8000000 in
include hp in
/-- **`uextend (fcmp)`** (`rule_lower_1283`) over typed contexts. -/
theorem uextend_fcmp_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1283 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h655 hres
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨uty, z, rfl, hety, rfl⟩ := instData_uextend_inv hdat
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  rename_i hj _ hi2 hd2
  obtain ⟨cl, hcl, hdat2⟩ := ctxInv_clifTI hctx hj hi2
  rw [← hd2] at hdat2
  obtain ⟨cc, ty', x, y, rfl, -, hok, hd3⟩ := instData_fcmp_inv hdat2
  simp only [List.cons.injEq] at hd3
  obtain ⟨hv7, hvcc⟩ := hd3
  subst hv7
  obtain ⟨hvcc, -⟩ := hvcc
  subst hvcc
  isel_inv_simp [] at *
  isel_destruct
  subst_vars
  obtain ⟨h655⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 123 655 _ _ _ _) := ⟨‹_›⟩
  obtain ⟨h715⟩ : Nonempty (ApplyInternal p (sem ctx) cfg _ 27 715 _ _ _ _) := ⟨‹_›⟩
  have hEc := emit_fcmp_okT (F := F) (isem := isem) hp hco hctx (hn := by omega) hok hvb h655
  obtain ⟨m0, cond, hflag, rfl, hst⟩ := lcrb_ok hp hco (hn := by omega) hEc.shape h715
  isel_call hp hco [cmp_output_reg_ok]
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_lcrb hR hEc hflag
  rw [hst]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ w vals cm' _ hh hdf ho
  obtain ⟨v, hzv, -, rfl, rfl⟩ := evalInst_uextend_ok ho
  obtain ⟨vals2, hev, hl⟩ := hdf.1 z _ _ _ v hj hi2 hcl rfl hzv
  obtain ⟨t, hv, -, hT⟩ := evalInst_fcmp_ok (hev default)
  subst hv
  have hv2 := lookup_zip_single hl
  subst hv2
  obtain ⟨hu, hr⟩ := hsem fr ρ t hh hdf hT
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr w).imp fun ρ' _ _ h => by
    rw [h]; exact vholds_uextend_bool8 hety _⟩

end Root

end Backend.Proof
