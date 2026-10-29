module

public import FV.Backend.Proof.IselCmpRoot
public import FV.Backend.Proof.IselFamALUATI
public import FV.Backend.Proof.IselFloatCmpEmit

@[expose] public section

/-!
# S11f: the `fcmp` root rules

`rule_lower_2176` (`lower.isle:2176`) lowers `fcmp cc ty [x, y]` to
`output_reg (lower_cond_result_bool (emit_fcmp cc x y))`, and `rule_lower_1283`
(`lower.isle:1283`) lowers `uextend ty (fcmp cc ty' [x, y])` the same way. Both leave the
condition of `emit_fcmp` (`emit_fcmp_okT`) as a 0/1 register (`condCode_lcrb`), which holds
CLIF's `fcmp` truth (`fcmp_truthy`) resp. its `uextend` (`vholds_uextend_bool8`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The roots -/

section Root
variable {p : Program} (hp : Data p) {F : BitVec 64 → Prop} {isem : Sem} (MR : MemRelT)
  (env : Clif.Env) (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR)
include hp hR hMR

set_option maxHeartbeats 8000000 in
/-- **`fcmp` of `f32`/`f64`** (`rule_lower_2176`, `lower.isle:2176`): the condition of
`emit_fcmp` as a 0/1 register. -/
theorem fcmp_okT : LowerRuleOkT isem MR env cp p rule_lower_2176 := by
  intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
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
  have hE := emit_fcmp_okT (F := F) (isem := isem) hp hco hctx (hn := by omega) hok hvb h655
  obtain ⟨m0, cond, hflag, rfl, hst⟩ := lcrb_ok hp hco (hn := by omega) hE.shape h715
  isel_call hp hco [cmp_output_reg_ok]
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_lcrb hR hE hflag
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
/-- **`uextend (fcmp)`** (`rule_lower_1283`, `lower.isle:1283`): the condition of `emit_fcmp`
as a 0/1 register, zero-extended. -/
theorem uextend_fcmp_okT : LowerRuleOkT isem MR env cp p rule_lower_1283 := by
  intro f ctx hctx ii info inst hi hic _ cfg hco m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
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
  have hE := emit_fcmp_okT (F := F) (isem := isem) hp hco hctx (hn := by omega) hok hvb h655
  obtain ⟨m0, cond, hflag, rfl, hst⟩ := lcrb_ok hp hco (hn := by omega) hE.shape h715
  isel_call hp hco [cmp_output_reg_ok]
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_lcrb hR hE hflag
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

/-! ## The registry -/

/-- The `fcmp` root rules of `lower` (S11f): `fcmp` (951) and `uextend (fcmp)` (812). -/
def floatCmpRootRule (r : Rule) : Bool :=
  r.id == 951 || r.id == 812

/-- **S11f's target (float comparisons)**: over float-capable contexts (`CtxInvT`), the
`fcmp` and `uextend (fcmp)` roots are correct. -/
def LowerRulesCorrectFC (p : Program) : Prop :=
  ∀ (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env) (cp : Clif.Program),
    Refines F isem → MRStable F MR →
    ∀ r ∈ p.rulesOf TId.lower, floatCmpRootRule r = true → LowerRuleOkT isem MR env cp p r

/-- The `fcmp` root rules of `lower`, in order. -/
theorem lower_floatCmpRoot_filter : (program.rulesOf TId.lower).filter floatCmpRootRule =
    [rule_lower_1283, rule_lower_2176] := by
  rw [program_rulesOf_686]
  rfl

/-- **S11f's target (float comparisons)**: over float-capable contexts, the `fcmp` roots are
correct. -/
theorem lowerRulesCorrectFC_program : LowerRulesCorrectFC program := by
  intro F isem MR env cp hR hMR r hr hfc
  have hp := data_program
  have hsub : r ∈ (program.rulesOf TId.lower).filter floatCmpRootRule :=
    List.mem_filter.2 ⟨hr, hfc⟩
  rw [lower_floatCmpRoot_filter] at hsub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hsub
  rcases hsub with rfl | rfl
  · exact uextend_fcmp_okT hp MR env cp hR hMR
  · exact fcmp_okT hp MR env cp hR hMR

end Backend.Proof
