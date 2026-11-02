import FV.Backend.Proof.IselFamAluBIconst
import FV.Backend.Proof.IselBaseTI

/-!
# `IselFamAluBIconst` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBIconst`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Isle Isle.Interp Isle.Aarch64
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
section
variable (st : LState) (tr : Array RuleId) (n : Nat)
end
include hp in
/-- **`iconst`** (`lower.isle:53`), i8..i64: the `imm` sequence. -/
theorem iconst_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_53 := by
  intro f ctx hctxT ii info inst hi hic hE cfg hco m n st tr env' s1 out st' tr' hm hn hvb _
      hmatch heval
  have _hE := hE
  have hctx : CtxInvT f ctx := hctxT.inv
  have hops := hctx.intOps ii info inst hi hic
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 50 := ⟨n - 50, by omega⟩
  obtain ⟨info', fs, hi', hd⟩ := root_match_data hp ctx (r := rule_lower_53) rfl hp.t2482
    term_2482_kind hp.t2341 term_2341_kind (m := m' + 1) hmatch
  rw [hi] at hi'
  cases hi'
  have hdat := hctx.data ii info inst hi hic
  rw [hd] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [fb_variantNames_UnaryImm] at hf
  rw [fb_variantNames_Iconst] at ho
  have hnm : instNames inst = ("UnaryImm", "Iconst") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, imm, rfl⟩ := fb_instNames_iconst hnm
  obtain ⟨hety, rfl⟩ := fb_instData_iconst hdat
  obtain ⟨tys, htys, hres, -⟩ := hctx.resTys ii info _ hi hic
  simp only [Clif.Inst.resultTypes, Option.some.injEq] at htys
  subst htys
  have hhead : info.resTys.head? = some (.int ty.width) := by
    rw [hres]; simp [ofClif_int_width (isInt_of_eTy hety)]
  have hw := eTy_width hety
  rw [match_53 hp ctx st tr m' hi hhead hd] at hmatch
  simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at hmatch
  obtain ⟨rfl, rfl⟩ := hmatch
  obtain ⟨v, s2, hA, hout⟩ := rhs_53_inv hp ctx hco st tr n' heval
  obtain ⟨ms, d, rfl, hsh, hrun⟩ :=
    imm_ok hp ctx hco hR (eTy_widths hety) (.inr rfl) (n := n' + 7) hA
  obtain ⟨rfl, hs'⟩ := hout _ rfl
  simp only at hs'
  subst hs'
  refine ⟨ms, _, hsh.emitted, rfl, ?_⟩
  refine lowerInstOk_one_fb hMR hsh.mono hsh.defs rfl ?_
  intro fr cm ρ vals cm' _ _ _ ho
  simp only [instOutcome, Clif.evalInst, pure, Except.pure] at ho
  cases ho
  obtain ⟨ρ', X, hp', hx, hX, -⟩ := hrun ρ
  refine ⟨rfl, usesOk_of [] ?_ (by simp), .inl hsh.res, _, ρ', rfl, hp', ?_⟩
  · intro mi hmi u hu
    rcases hsh.uses mi hmi u hu with h | h
    · exact .inl h
    · exact .inl (by omega)
  · refine vholds_of_lo64 hw hx ?_
    have hp64 : 2 ^ ty.width ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
    rw [hX, fb_u64_imm64 hw, fb_u64_nat (by have := imm.isLt; omega), Nat.mod_eq_of_lt imm.isLt]

end Backend.Proof
