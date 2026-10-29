module

public import FV.Backend.Proof.IselFamAluBClz
public import FV.Backend.Proof.IselBaseTI
public import FV.Backend.Proof.IselFamAluBBaseTI

@[expose] public section

/-!
# `IselFamAluBClz` over typed contexts (S11e5 Stage C, slice 7)

The `CtxInv` proofs of `IselFamAluBClz`, restated over float-capable contexts (`CtxT`, `LowerRuleOkTI`):
the values whose registers they use are in integer positions (`CtxInvT.valueRegI`, `int_posA`).
-/

namespace Backend.Proof
theorem ite_sub_bvTI {n : Nat} (c : Prop) [Decidable c] (a b k : BitVec n) :
    (if c then a else b) - k = if c then a - k else b - k := by
  split <;> rfl

open Isle Isle.Interp Isle.Aarch64
variable {p : Program} (hp : Data p) (ctx : Ctx) {cfg : Config} (hc : cfg.checkOverlap = false)
section
variable (st : LState) (tr : Array RuleId) (n : Nat)
end
include hp in
/-- **`clz.i32`/`clz.i64`** (`lower.isle:1961`): one `clz`. At i8/i16 the earlier rules `1951`/`1955` match.** -/

theorem clz_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1961 :=
  unary_ruleOkTI hp (cop := .clz) rfl hp.t2391 term_2391_kind variantNames_Clz rfl
    (fun w x => env2 (.ty (.int w)) (.value x)) (fun w => w ≠ 8 ∧ w ≠ 16) (fun _ _ => True)
    (fun _ _ => 1) (fun w _ b x => [.bitRR .clz (szOf w) (.vreg b .int) (.vreg x .int)])
    (fun _ _ b => b)
    (fun ctx _ ii _ w _ st tr m _ _ hi hty _ hd hfirst h => by
      rw [match_1961 hp ctx st tr m hi hty hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      refine ⟨h.1.symm, h.2.symm, ?_, ?_⟩
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1961 hp) (lower_idx_1951 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1951 hp ctx st tr k hi hty hd] at h'; cases h'
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1961 hp) (lower_idx_1955 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1955 hp ctx st tr k hi hty hd] at h'; cases h')
    (fun ctx _ _ _ st tr n hc hx hw _ _ => by
      obtain ⟨tr', h⟩ := rhs_1961 hp ctx hc st tr n hx hw
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1961_none hp ctx st tr n hx v s'
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
        simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary, Clif.Sem.clz,
            Clif.Ty.width, ne_eq, not_true_eq_false, false_and, and_false, false_implies] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        intro _ <;>
        simp [BitVec.setWidth_setWidth_of_le])

include hp in
/-- **`ctz.i32`/`ctz.i64`** (`lower.isle:1995`): `rbit`, `clz`. At i8/i16 the earlier rules `1982`/`1986` match.** -/
theorem ctz_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1995 :=
  unary_ruleOkTI hp (cop := .ctz) rfl hp.t2393 term_2393_kind variantNames_Ctz rfl
    (fun w x => env2 (.ty (.int w)) (.value x)) (fun w => w ≠ 8 ∧ w ≠ 16) (fun _ _ => True)
    (fun _ _ => 2) (fun w _ b x => [.bitRR .rbit (szOf w) (.vreg b .int) (.vreg x .int), .bitRR .clz (szOf w) (.vreg (b + 1) .int) (.vreg b .int)])
    (fun _ _ b => b + 1)
    (fun ctx _ ii _ w _ st tr m _ _ hi hty _ hd hfirst h => by
      rw [match_1995 hp ctx st tr m hi hty hd] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
      refine ⟨h.1.symm, h.2.symm, ?_, ?_⟩
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1995 hp) (lower_idx_1982 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1982 hp ctx st tr k hi hty hd] at h'; cases h'
      · rintro rfl
        obtain ⟨pre, post, hL, hmem⟩ := earlier_of_idx (lower_idx_1995 hp) (lower_idx_1986 hp)
          (by decide)
        obtain ⟨m', hm', s', h'⟩ := hfirst pre post hL _ hmem
        obtain ⟨k, rfl⟩ : ∃ k, m' = k + 2 := ⟨m' - 2, by omega⟩
        rw [match_1986 hp ctx st tr k hi hty hd] at h'; cases h')
    (fun ctx _ _ _ st tr n hc hx hw _ _ => by
      obtain ⟨tr', h⟩ := rhs_1995 hp ctx hc st tr n hx hw
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1995_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hety _ hP _ _ _ hu => by
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl) (prun_nil _)), ?_⟩
      have hu' : (ρ x).setWidth ty.width = u := hu
      subst hu'
      revert hP
      generalize hs : szOf (Clif.Ty.width ty) = sz at *
      cases ty <;> simp [eTy] at hety <;> simp [szOf, Clif.Ty.width] at hs <;> subst hs <;>
        simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary, Clif.Sem.ctz,
            BitVec.ctz, Clif.Ty.width, ne_eq, not_true_eq_false, false_and, and_false,
            false_implies] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        intro _ <;>
        simp [BitVec.setWidth_setWidth_of_le])

include hp in
/-- **`ctz.i8`** (`lower.isle:1982`).** -/
theorem ctz_i8_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1982 :=
  unary_ruleOkTI hp (cop := .ctz) rfl hp.t2393 term_2393_kind variantNames_Ctz rfl
    (fun _ x => env1 (.value x)) (fun w => w = 8) (fun _ _ => True) (fun _ _ => 3)
    (fun _ _ b x => [.bitRR .rbit .size32 (.vreg b .int) (.vreg x .int),
      .aluRRImmLogic .orr .size32 (.vreg (b + 1) .int) (.vreg b .int) ⟨8388608, .size32⟩,
      .bitRR .clz .size32 (.vreg (b + 2) .int) (.vreg (b + 1) .int)])
    (fun _ _ b => b + 2)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 8
      · subst hw
        rw [match_1982 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1982_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_1982 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1982_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hE _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i8) hP (by decide) hE
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl)
        (prun_rr hR rfl (fun _ => rfl) (prun_nil _))), ?_⟩
      have hu' : (ρ x).setWidth 8 = u := hu
      subst hu'
      simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary, Clif.Sem.ctz,
          BitVec.ctz] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        (try unfold OperandSize.bits at *) <;>
        simp [BitVec.clz, BitVec.clzAuxRec_succ, BitVec.clzAuxRec_zero,
          BitVec.getElem_reverse, BitVec.getMsbD_setWidth, apply_ite (BitVec.setWidth 8)])

include hp in
/-- **`ctz.i16`** (`lower.isle:1986`).** -/
theorem ctz_i16_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1986 :=
  unary_ruleOkTI hp (cop := .ctz) rfl hp.t2393 term_2393_kind variantNames_Ctz rfl
    (fun _ x => env1 (.value x)) (fun w => w = 16) (fun _ _ => True) (fun _ _ => 3)
    (fun _ _ b x => [.bitRR .rbit .size32 (.vreg b .int) (.vreg x .int),
      .aluRRImmLogic .orr .size32 (.vreg (b + 1) .int) (.vreg b .int) ⟨32768, .size32⟩,
      .bitRR .clz .size32 (.vreg (b + 2) .int) (.vreg (b + 1) .int)])
    (fun _ _ b => b + 2)
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 16
      · subst hw
        rw [match_1986 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1986_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx _ _ _ st tr n hc hx _ _ _ => by
      obtain ⟨tr', h⟩ := rhs_1986 hp ctx hc st tr n hx
      exact ⟨tr', _, h, by st_facts, by st_facts⟩)
    (fun ctx _ _ _ st tr n v s' hx => by
      rcases hx with hx | hx
      · exact rhs_1986_none hp ctx st tr n hx v s'
      · exact absurd trivial hx)
    (fun _ _ _ => by omega) (by code_facts) (by code_facts)
    F isem MR env cp hMR
    (fun ty _ b x ρ u hE _ hP _ _ _ hu => by
      obtain rfl := ty_eq_of_width (ty' := .i16) hP (by decide) hE
      refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl)
        (prun_rr hR rfl (fun _ => rfl) (prun_nil _))), ?_⟩
      have hu' : (ρ x).setWidth 16 = u := hu
      subst hu'
      simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary, Clif.Sem.ctz,
          BitVec.ctz] at * <;>
        dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
        (try unfold OperandSize.bits at *) <;>
        simp [BitVec.clz, BitVec.clzAuxRec_succ, BitVec.clzAuxRec_zero,
          BitVec.getElem_reverse, BitVec.getMsbD_setWidth, apply_ite (BitVec.setWidth 16)])

set_option maxHeartbeats 1000000 in
include hp in
/-- **`clz.i8`** (`lower.isle:1951`).** -/
theorem clz_i8_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1951 :=
  unary_ruleOkTI' hp (cop := .clz) rfl hp.t2391 term_2391_kind variantNames_Clz rfl
    (fun _ x => env1 (.value x)) (fun w => w = 8) F isem MR env cp hMR
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 8
      · subst hw
        rw [match_1951 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1951_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx cfg _ _ st tr n v s' _ hT => by
      have := rhs_1951_fail hp ctx (cfg := cfg) st tr (n + 120) (.inl hT) v s'
      rwa [show n + 120 + 80 = n + 200 by omega] at this)
    (fun ctx cfg x w st tr n v s' hc hx _ _ hP he => by
      subst hP
      cases hT : ctx.valueType? x with
      | none =>
        have := rhs_1951_fail hp ctx (cfg := cfg) st tr (n + 120) (.inl hT) v s'
        rw [show n + 120 + 80 = n + 200 by omega] at this
        exact absurd he this
      | some t =>
      by_cases h32 : t = .int 32
      · subst h32
        obtain ⟨tr', h⟩ := rhs_1951_pass hp ctx hc st tr (n + 120) hx hT (.inl rfl)
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.bitRR .clz .size32 (.vreg st.nextVreg .int) (.vreg x .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) ⟨24, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty _ _ _ hT'
        rcases hT' with h | h <;> simp at h
      by_cases h64 : t = .int 64
      · subst h64
        obtain ⟨tr', h⟩ := rhs_1951_pass hp ctx hc st tr (n + 120) hx hT (.inr rfl)
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.bitRR .clz .size32 (.vreg st.nextVreg .int) (.vreg x .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) ⟨24, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty _ _ _ hT'
        rcases hT' with h | h <;> simp at h
      by_cases hb : t.bits ≤ 32
      · obtain ⟨tr', h⟩ := rhs_1951_ext hp ctx hc st tr (n + 120) hx hT h32 h64 hb
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.extend (.vreg st.nextVreg .int) (.vreg x .int) false t.bits 32, .bitRR .clz .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int) ⟨24, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty hty hE _ hT' ρ u hu
        have ht : t = .int 8 := by rcases hT' with h | h <;> simp_all
        subst ht
        obtain rfl := ty_eq_of_width (ty' := .i8) hty (by decide) hE
        refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl)
          (prun_rr hR rfl (fun _ => rfl) (prun_nil _))), ?_⟩
        have hu' : (ρ x).setWidth 8 = u := hu
        subst hu'
        simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary, Clif.Sem.clz,
            CTy.bits, Imm12.value] at * <;>
          dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
          (try unfold OperandSize.bits at *) <;>
          simp [BitVec.clz, BitVec.clzAuxRec_succ, BitVec.clzAuxRec_zero,
            ite_sub_bvTI, apply_ite (BitVec.setWidth 8)]
      · have := rhs_1951_fail hp ctx (cfg := cfg) st tr (n + 120) (.inr ⟨t, hT, h32, h64, hb⟩) v s'
        rw [show n + 120 + 80 = n + 200 by omega] at this
        exact absurd he this)

set_option maxHeartbeats 1000000 in
include hp in
/-- **`clz.i16`** (`lower.isle:1955`).** -/
theorem clz_i16_okTI (F : BitVec 64 → Prop) (isem : Sem) (MR : MemRelT) (env : Clif.Env)
    (cp : Clif.Program) (hR : Refines F isem) (hMR : MRStable F MR) :
    LowerRuleOkTI isem MR env cp p rule_lower_1955 :=
  unary_ruleOkTI' hp (cop := .clz) rfl hp.t2391 term_2391_kind variantNames_Clz rfl
    (fun _ x => env1 (.value x)) (fun w => w = 16) F isem MR env cp hMR
    (fun ctx _ _ _ w _ st tr m _ _ hi hty _ hd _ h => by
      by_cases hw : w = 16
      · subst hw
        rw [match_1955 hp ctx st tr m hi hty hd] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        exact ⟨h.1.symm, h.2.symm, rfl⟩
      · rw [match_1955_ne hp ctx st tr m hi hty hw hd] at h; cases h)
    (fun ctx cfg _ _ st tr n v s' _ hT => by
      have := rhs_1955_fail hp ctx (cfg := cfg) st tr (n + 120) (.inl hT) v s'
      rwa [show n + 120 + 80 = n + 200 by omega] at this)
    (fun ctx cfg x w st tr n v s' hc hx _ _ hP he => by
      subst hP
      cases hT : ctx.valueType? x with
      | none =>
        have := rhs_1955_fail hp ctx (cfg := cfg) st tr (n + 120) (.inl hT) v s'
        rw [show n + 120 + 80 = n + 200 by omega] at this
        exact absurd he this
      | some t =>
      by_cases h32 : t = .int 32
      · subst h32
        obtain ⟨tr', h⟩ := rhs_1955_pass hp ctx hc st tr (n + 120) hx hT (.inl rfl)
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.bitRR .clz .size32 (.vreg st.nextVreg .int) (.vreg x .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) ⟨16, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty _ _ _ hT'
        rcases hT' with h | h <;> simp at h
      by_cases h64 : t = .int 64
      · subst h64
        obtain ⟨tr', h⟩ := rhs_1955_pass hp ctx hc st tr (n + 120) hx hT (.inr rfl)
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.bitRR .clz .size32 (.vreg st.nextVreg .int) (.vreg x .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int) ⟨16, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty _ _ _ hT'
        rcases hT' with h | h <;> simp at h
      by_cases hb : t.bits ≤ 32
      · obtain ⟨tr', h⟩ := rhs_1955_ext hp ctx hc st tr (n + 120) hx hT h32 h64 hb
        rw [show n + 120 + 80 = n + 200 by omega, he] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨[.extend (.vreg st.nextVreg .int) (.vreg x .int) false t.bits 32, .bitRR .clz .size32 (.vreg (st.nextVreg + 1) .int) (.vreg st.nextVreg .int), .aluRRImm12 .sub .size32 (.vreg (st.nextVreg + 2) .int) (.vreg (st.nextVreg + 1) .int) ⟨16, false⟩], _, rfl, ⟨by st_facts, by st_facts, by st_facts, by code_facts0, by code_facts0⟩,
          ?_⟩
        intro ty hty hE _ hT' ρ u hu
        have ht : t = .int 16 := by rcases hT' with h | h <;> simp_all
        subst ht
        obtain rfl := ty_eq_of_width (ty' := .i16) hty (by decide) hE
        refine ⟨_, prun_rr hR rfl (fun _ => rfl) (prun_rr hR rfl (fun _ => rfl)
          (prun_rr hR rfl (fun _ => rfl) (prun_nil _))), ?_⟩
        have hu' : (ρ x).setWidth 16 = u := hu
        subst hu'
        simp only [VHolds, resX, opnd, ofX, lo64, upd, ↓reduceIte, Clif.Sem.unary, Clif.Sem.clz,
            CTy.bits, Imm12.value] at * <;>
          dsimp only [Clif.Ty.width, OperandSize.bits] at * <;>
          (try unfold OperandSize.bits at *) <;>
          simp [BitVec.clz, BitVec.clzAuxRec_succ, BitVec.clzAuxRec_zero,
            ite_sub_bvTI, apply_ite (BitVec.setWidth 16)]
      · have := rhs_1955_fail hp ctx (cfg := cfg) st tr (n + 120) (.inr ⟨t, hT, h32, h64, hb⟩) v s'
        rw [show n + 120 + 80 = n + 200 by omega] at this
        exact absurd he this)

end Backend.Proof
