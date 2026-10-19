import FV.Backend.Proof.IselFamAluBUnary
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselFamAluBBaseTI

/-!
# `IselFamAluBUnary` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBUnary`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Isle Isle.Interp Isle.Aarch64
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
include hp in
/-- **`ineg_base_case`** (`lower.isle:857`), i8..i64: `sub wd, wzr, wn` / `sub xd, xzr, xn`. -/
theorem ineg_base_case_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_857 :=
  unary_ruleOkTI hp (cop := .ineg) rfl hp.t2359 term_2359_kind variantNames_Ineg rfl
    (fun w x => env2 (.ty (.int w)) (.value x)) (fun _ => True) (fun _ _ => True) (fun _ _ => 1)
    (fun w _ b x => [.aluRRR .sub (szOf w) (.vreg b .int) .xzr (.vreg x .int)]) (fun _ _ b => b)
    (fun ctx _ _ _ _ _ st tr m _ _ hi hty hw hd _ h => by
      rw [match_857 hp ctx hi hty hw hd st tr m] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      exact ⟨h.1.symm, h.2.symm, trivial⟩)
    (fun ctx _ _ _ st tr n hc hx hw _ _ => by
      obtain ⟨tr', h⟩ := rhs_857 hp ctx hc hx hw st tr n
      exact ⟨tr', _, h, by simp [LState.emit, LState.fresh], rfl⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_857_none hp ctx hx st tr n v s'
      · exact absurd trivial hx)
    (fun _ _ _ => Nat.le_refl _)
    (fun _ _ b _ mi hmi d hd => by
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [(vdefs_rr rfl).1] at hd; simp at hd; omega)
    (fun _ _ b x mi hmi u hu => by
      simp only [List.mem_singleton] at hmi; subst hmi
      rw [(vdefs_rr rfl).2] at hu; simp at hu; exact .inr hu)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hety _ _ _ _ _ hu => ⟨_, prun_rr hR rfl (fun w => ispec_xzr_sub _ _ _ _ w)
      (prun_nil _), by
        have hu' : (ρ x).setWidth ty.width = u := hu
        subst hu'
        generalize hs : szOf (Clif.Ty.width ty) = sz at *
        cases ty <;> simp [eTy] at hety <;> simp [szOf, Clif.Ty.width] at hs <;> subst hs <;>
          simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary,
            Clif.Sem.ineg] at * <;>
          dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
          (try unfold OperandSize.bits Clif.Ty.width at *) <;>
          bv_omega⟩)

end Backend.Proof
