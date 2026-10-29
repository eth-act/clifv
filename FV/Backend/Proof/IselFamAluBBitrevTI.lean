module

public import FV.Backend.Proof.IselFamAluBBitrev
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselFamAluBBaseTI

@[expose] public section

/-!
# `IselFamAluBBitrev` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBBitrev`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
open Isle Isle.Interp Isle.Aarch64
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
section
variable (st : LState) (tr : Array RuleId) (n : Nat)
end
include hp in
/-- **`bitrev.i8`** (`lower.isle:1931`). -/
theorem bitrev_i8_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1931 :=
  unary_ruleOkTI hp (cop := .bitrev) rfl hp.t2390 term_2390_kind variantNames_Bitrev rfl
    (fun _ x => env1 (.value x)) (fun w => w = 8) (fun _ _ => True) (fun _ _ => 2)
    (fun _ _ b x => [.bitRR .rbit .size32 (.vreg b .int) (.vreg x .int),
      .aluRRImmShift .lsr .size32 (.vreg (b + 1) .int) (.vreg b .int) 24]) (fun _ _ b => b + 1)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases h8 : w = 8
      · subst h8
        rw [match_1931 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1931_ne hp ctx st tr m hi hty h8 hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_1931 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1931_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hE _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i8) hP (by decide) hE
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl) (prun_nil _)), ?_⟩
      have hu' : (ρ x).setWidth 8 = u := hu
      subst hu'
      simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary,
          Clif.Sem.bitrev] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        (try unfold OperandSize.bits at *) <;>
        apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
        repeat (first | omega |
          (rcases i with _ | i; · simp [BitVec.getElem_ushiftRight, BitVec.getElem_reverse,
            BitVec.getMsbD_setWidth])))

include hp in
/-- **`bitrev.i16`** (`lower.isle:1937`). -/
theorem bitrev_i16_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1937 :=
  unary_ruleOkTI hp (cop := .bitrev) rfl hp.t2390 term_2390_kind variantNames_Bitrev rfl
    (fun _ x => env1 (.value x)) (fun w => w = 16) (fun _ _ => True) (fun _ _ => 2)
    (fun _ _ b x => [.bitRR .rbit .size32 (.vreg b .int) (.vreg x .int),
      .aluRRImmShift .lsr .size32 (.vreg (b + 1) .int) (.vreg b .int) 16]) (fun _ _ b => b + 1)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases h16 : w = 16
      · subst h16
        rw [match_1937 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1937_ne hp ctx st tr m hi hty h16 hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_1937 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1937_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hE _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i16) hP (by decide) hE
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl) (prun_nil _)), ?_⟩
      have hu' : (ρ x).setWidth 16 = u := hu
      subst hu'
      simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary,
          Clif.Sem.bitrev] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        (try unfold OperandSize.bits at *) <;>
        apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
        repeat (first | omega |
          (rcases i with _ | i; · simp [BitVec.getElem_ushiftRight, BitVec.getElem_reverse,
            BitVec.getMsbD_setWidth])))

include hp in
/-- **`bitrev.i32`/`bitrev.i64`** (`lower.isle:1946`): a single `rbit`. At i8/i16 the rules
`1931`/`1937`, earlier in `lower`'s order, match, so this rule is not selected there. -/
theorem bitrev_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1946 :=
  unary_ruleOkTI hp (cop := .bitrev) rfl hp.t2390 term_2390_kind variantNames_Bitrev rfl
    (fun w x => env2 (.ty (.int w)) (.value x)) (fun w => w ≠ 8 ∧ w ≠ 16) (fun _ _ => True)
    (fun _ _ => 1) (fun w _ b x => [.bitRR .rbit (szOf w) (.vreg b .int) (.vreg x .int)])
    (fun _ _ b => b)
    (fun ctx _ ii _ w _ st tr m _ _ hi hty _ hd hfirst h => by
      rw [match_1946 hp ctx st tr m hi hty hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      refine ⟨h.1.symm, h.2.symm, ?_, ?_⟩
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1946 hp) (lower_idx_1931 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1931 hp ctx st tr k hi hty hd] at h'; cases h'
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1946 hp) (lower_idx_1937 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1937 hp ctx st tr k hi hty hd] at h'; cases h')
    (fun ctx _ _ _ st tr n hc hx hw _ _ => by
      obtain ⟨tr', h⟩ := rhs_1946 hp ctx hc st tr n hx hw
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1946_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hety _ hP _ _ _ hu => by
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_nil _), ?_⟩
      have hu' : (ρ x).setWidth ty.width = u := hu
      subst hu'
      revert hP
      generalize hs : szOf (Clif.Ty.width ty) = sz at *
      cases ty <;> simp [eTy] at hety <;> simp [szOf, Clif.Ty.width] at hs <;> subst hs <;>
        simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary, Clif.Sem.bitrev,
            Clif.Ty.width, ne_eq, not_true_eq_false, false_and, and_false, false_implies] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        intro _ <;>
        (try unfold OperandSize.bits at *) <;>
        apply BitVec.eq_of_getElem_eq <;> intro i hi <;>
        repeat (first | omega |
          (rcases i with _ | i; · simp [BitVec.getElem_reverse, BitVec.getMsbD_setWidth])))

end Backend.Proof
