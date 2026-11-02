import FV.Backend.Proof.IselFamAluBBswap
import FV.Backend.Proof.IselBaseTI
import FV.Backend.Proof.IselFamAluBBaseTI

/-!
# `IselFamAluBBswap` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBBswap`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Isle Isle.Interp Isle.Aarch64
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
section
variable (st : LState) (tr : Array RuleId) (n : Nat)
end
include hp in
/-- **`bswap.i16`** (`lower.isle:2035`). -/
theorem bswap_i16_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2035 :=
  unary_ruleOkTI hp (cop := .bswap) rfl hp.t2394 term_2394_kind variantNames_Bswap rfl
    (fun _ x => env1 (.value x)) (fun w => w = 16) (fun _ _ => True) (fun _ _ => 1)
    (fun _ _ b x => [.bitRR .rev16 .size32 (.vreg b .int) (.vreg x .int)]) (fun _ _ b => b)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 16
      · subst hw
        rw [match_2035 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_2035_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_2035 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_2035_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hE _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i16) hP (by decide) hE
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩
      have hu' : (ρ x).setWidth 16 = u := hu
      subst hu'
      simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary, rev16w] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        simp only [bswap_16] <;>
        (try unfold OperandSize.bits at *) <;>
        apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
        repeat (first | omega |
          (rcases i with _ | i; · simp [BitVec.getElem_ushiftRight, BitVec.getElem_shiftLeft])))

include hp in
/-- **`bswap.i32`** (`lower.isle:2038`). -/
theorem bswap_i32_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2038 :=
  unary_ruleOkTI hp (cop := .bswap) rfl hp.t2394 term_2394_kind variantNames_Bswap rfl
    (fun _ x => env1 (.value x)) (fun w => w = 32) (fun _ _ => True) (fun _ _ => 1)
    (fun _ _ b x => [.bitRR .rev32 .size32 (.vreg b .int) (.vreg x .int)]) (fun _ _ b => b)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 32
      · subst hw
        rw [match_2038 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_2038_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_2038 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_2038_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hE _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i32) hP (by decide) hE
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩
      have hu' : (ρ x).setWidth 32 = u := hu
      subst hu'
      simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        simp [BitVec.setWidth_setWidth_of_le])

include hp in
/-- **`bswap.i64`** (`lower.isle:2041`). -/
theorem bswap_i64_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_2041 :=
  unary_ruleOkTI hp (cop := .bswap) rfl hp.t2394 term_2394_kind variantNames_Bswap rfl
    (fun _ x => env1 (.value x)) (fun w => w = 64) (fun _ _ => True) (fun _ _ => 1)
    (fun _ _ b x => [.bitRR .rev64 .size64 (.vreg b .int) (.vreg x .int)]) (fun _ _ b => b)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 64
      · subst hw
        rw [match_2041 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_2041_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_2041 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_2041_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hE _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i64) hP (by decide) hE
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩
      have hu' : (ρ x).setWidth 64 = u := hu
      subst hu'
      simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        simp [BitVec.setWidth_setWidth_of_le])

end Backend.Proof
