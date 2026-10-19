import FV.Backend.Proof.IselCmpSelect
import FV.Backend.Proof.IselBaseTI

/-!
# `IselCmpSelect` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselCmpSelect`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
section
variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
end
/-- A `select` of subset E has an E type. -/
theorem select_eTyTI {ty : Clif.Ty} {c x y : Nat}
    (hE : Compile.instE (.select ty c x y) = true) : eTy ty = true := by
  simpa [Compile.instE, Compile.tyE, eTy] using hE

/-- The operands of an integer `select` are all in integer positions. -/
theorem intArgs_select_int {ty : Clif.Ty} {c x y : Nat} (h : ty.isFloat = false) :
    intArgs (.select ty c x y) = [c, x, y] := by
  show (if ty.isFloat then [c] else [c, x, y]) = _
  rw [h]; rfl

section Root
variable {p : Program} (hp : Data p)
set_option maxHeartbeats 8000000 in
include hp in
theorem select_ruleOkTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2267 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 10 := ⟨m - 10, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  isel_inv' hp [] at hmatch heval
  rename_i hins hdd h650 h659
  obtain ⟨hout⟩ : Nonempty (externCtor ctx T.output _ _ = _) := ⟨‹_›⟩
  obtain ⟨hva⟩ : Nonempty (externExtract ctx T.value_array_3 _ st = _) := ⟨‹_›⟩
  rw [hi, Option.some.injEq] at hins
  subst hins
  have hdat := hctx.data ii _ inst hi hic
  rw [← hdd] at hdat
  obtain ⟨ty, c, x, y, rfl, -, rfl⟩ := instData_select_inv hdat
  have hety := select_eTyTI hE
  have hnf : ty.isFloat = false := by cases ty <;> simp_all [eTy]
  rw [ext_value_array_3] at hva
  cases hva
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii _ _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  rw [hres] at h659
  simp only [List.map_cons, List.map_nil, List.head?_cons, Option.getD_some,
    ofClif_int_width (isInt_of_eTy hety)] at h659
  have hC := is_nonzero_cmp_okT hp hco hR hctx (hxi := hops c (by rw [intArgs_select_int hnf]; simp)) (hn := by omega) hvb h650
  obtain ⟨mf, cond, rx, ry, hflag, hrx, hry, rfl, hs⟩ :=
    lower_select_ok hp hco (hn := by omega) (cmp_eTy_widths hety) hC.shape h659
  rw [ctor_output'] at hout
  obtain ⟨rfl, rfl⟩ := hout
  have hx := hvb x rx hrx
  have hy := hvb y ry hry
  rw [hctx.valueRegI x rx hrx (hops x (by rw [intArgs_select_int hnf]; simp))] at hs
  rw [hctx.valueRegI y ry hry (hops y (by rw [intArgs_select_int hnf]; simp))] at hs
  obtain ⟨hmono, ms, hf, hsem⟩ := condCode_csel hR hC hflag hx hy
  rw [hs]
  refine ⟨ms, hf.emitted, _, rfl, lowerInstOk_runs hMR hf.mono hf.defs rfl ?_⟩
  intro fr cm ρ w vals cm' _ hh hdf ho
  obtain ⟨cv, a, b, hcv, hxa, hyb, rfl, rfl⟩ := evalInst_select_ok ho
  have hxv := getAs_ok hxa
  have hyv := getAs_ok hyb
  obtain ⟨hu, hr⟩ := hsem fr ρ _ hh hdf ⟨cv, hcv, rfl⟩ (by simp [hxv]) (by simp [hyv])
  exact ⟨rfl, hu, .inl hmono, _, rfl, (hr w).imp fun ρ' _ _ h => by
    rw [h]; exact vholds_select hety _ (hh _ _ hxv) (hh _ _ hyv)⟩

end Root
end Backend.Proof
