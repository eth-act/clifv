import FV.Backend.Proof.IselFamAluBIconst

/-!
# `IselTermsShift` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselTermsShift`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Backend Isle Isle.Interp Isle.Aarch64
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
section Extern
variable (st : LState)
end Extern
/-- `CtxInvT`: the looked-through definition is `iconst ty' imm`, with data `imm64OfIconst`. -/
theorem defInst_iconst_clifTI {f : Clif.Function} (hctx : CtxInvT f ctx) {y j : Nat} {info : IInfo}
    {fs : List V} (hd : ctx.defInst? y = some j) (hi : ctx.insts[j]? = some info)
    (hdata : info.data = .data 152 35 (.data 151 57 [] :: fs)) :
    ∃ ty imm, info.clif = some (.iconst ty imm) ∧ fs = [.int (imm64OfIconst ty imm)] := by
  have hs := hctx.defClif y j info hd hi
  obtain ⟨cl, hcl⟩ := Option.isSome_iff_exists.mp hs
  have hdat := hctx.data j info cl hi hcl
  rw [hdata] at hdat
  obtain ⟨hf, ho⟩ := instData_inv_names hdat
  rw [fb_variantNames_UnaryImm] at hf
  rw [fb_variantNames_Iconst] at ho
  have hnm : instNames cl = ("UnaryImm", "Iconst") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨ty, imm, rfl⟩ := fb_instNames_iconst hnm
  obtain ⟨-, hfs⟩ := fb_instData_iconst hdat
  exact ⟨ty, imm, hcl, hfs⟩

section
variable (st : LState) (tr : Array RuleId) (m : Nat)
end
end Backend.Proof
