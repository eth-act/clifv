import FV.Backend.Proof.IselShpBase

/-!
# Totality of the ISLE interpreter on total expressions

For any program `p` with `totalProg p = true` (every rule of a non-`partial` internal term has a
total right-hand side), any embedding and any configuration: a run of a total expression
(arguments, `let*` bindings) or of a call of a non-`partial` term that does not throw returns a
value (`totAt`, by induction on fuel). Only a `partial` term returns `none`: an external
non-`partial` constructor that fails throws, and an internal non-`partial` one with no matching
rule throws.

`totality`: the instance for the exported `program` (`totalProg_program`, by evaluation).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

section Generic
variable {V σ : Type} (p : Program) (sm : Isle.Interp.Sem V σ) (cfg : Config)

/-- A selected rule is one of the candidates (for any configuration). -/
theorem selectRule_mem :
    ∀ {n : Nat} {term : Term} {rs : List Rule} {vs : List V} {s s' : σ × Array RuleId}
      {r : Rule} {env : Env V},
      (selectRule p sm cfg n term rs vs).run s = .ok (some (r, env), s') → r ∈ rs
  | 0, _, _, _, _, _, _, _, h => by rw [selectRule.eq_1] at h; cases h
  | n + 1, _, [], _, _, _, _, _, h => by rw [selectRule.eq_2] at h; cases h
  | n + 1, term, r' :: rs, vs, s, s', r, env, h => by
    rw [selectRule.eq_3] at h
    obtain ⟨o, s1, h1, h2⟩ := bind_ok h
    cases o with
    | none => exact List.mem_cons_of_mem _ (selectRule_mem h2)
    | some env' =>
      simp only at h2
      split at h2
      · obtain ⟨others, s2, h3, h4⟩ := bind_ok h2
        split at h4
        · cases pure_ok h4; exact List.mem_cons_self ..
        · exact (throw_ok h4).elim
      · cases pure_ok h2; exact List.mem_cons_self ..

/-- A rule of a non-`partial` internal term has a total right-hand side. -/
theorem totalE_rhs (htp : totalProg p = true) {t : TermId} {term : Term} {flags : TermFlags}
    {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hp : flags.isPartial = false)
    {rl : Rule} (hmem : rl ∈ p.rulesOf t) : totalE p rl.rhs = true := by
  have hlt : t < p.ruleLists.size := by
    unfold Program.rulesOf at hmem
    refine Nat.lt_of_not_le fun hc => ?_
    rw [Array.getElem?_eq_none hc] at hmem
    simp at hmem
  have hall := List.all_eq_true.mp htp t (List.mem_range.mpr hlt)
  have hit : internalTotal p t = true := by
    unfold internalTotal; rw [ht]; simp only [hk, hp, Bool.not_false]
  rw [hit, Bool.not_true, Bool.false_or] at hall
  exact List.all_eq_true.mp hall rl hmem

/-- Totality at fuel `n`. -/
structure TotAt (n : Nat) : Prop where
  expr : ∀ e env s r s', totalE p e = true →
    (evalExpr p sm cfg n e env).run s = .ok (r, s') → r.isSome = true
  args : ∀ es env s r s', totalL p es = true →
    (evalArgs p sm cfg n es env).run s = .ok (r, s') → r.isSome = true
  binds : ∀ bs env s r s', totalB p bs = true →
    (evalBinds p sm cfg n bs env).run s = .ok (r, s') → r.isSome = true
  apply : ∀ ty t vs s r s', termTotal p t = true →
    (applyTerm p sm cfg n ty t vs).run s = .ok (r, s') → r.isSome = true

/-- **Totality at every fuel.** -/
theorem totAt (htp : totalProg p = true) : ∀ n, TotAt p sm cfg n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> rename_i h <;>
      first
      | (rw [evalExpr.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalArgs.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalBinds.eq_1] at h; exact (throw_ok h).elim)
      | (rw [applyTerm.eq_1] at h; exact (throw_ok h).elim)
  | succ n ih =>
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- evalExpr
    intro e env s r s' he h
    cases e with
    | var ty x =>
      rw [evalExpr.eq_2] at h
      split at h
      · cases pure_ok h; rfl
      · exact (throw_ok h).elim
    | constBool ty b => rw [evalExpr.eq_3] at h; cases pure_ok h; rfl
    | constInt ty i => rw [evalExpr.eq_4] at h; cases pure_ok h; rfl
    | constPrim ty nm =>
      rw [evalExpr.eq_5] at h
      split at h
      · cases pure_ok h; rfl
      · exact (throw_ok h).elim
    | «let» ty bs body =>
      rw [evalExpr.eq_6] at h
      simp only [totalE, Bool.and_eq_true] at he
      obtain ⟨o, s1, h1, h2⟩ := bind_ok h
      have hs := ih.binds _ _ _ _ _ he.1 h1
      cases o with
      | none => cases hs
      | some env' => exact ih.expr _ _ _ _ _ he.2 h2
    | term ty t args =>
      rw [evalExpr.eq_7] at h
      simp only [totalE, Bool.and_eq_true] at he
      obtain ⟨o, s1, h1, h2⟩ := bind_ok h
      have hs := ih.args _ _ _ _ _ he.2 h1
      cases o with
      | none => cases hs
      | some vs => exact ih.apply _ _ _ _ _ _ he.1 h2
  · -- evalArgs
    intro es env s r s' he h
    cases es with
    | nil => rw [evalArgs.eq_2] at h; cases pure_ok h; rfl
    | cons e es =>
      rw [evalArgs.eq_3] at h
      simp only [totalL, Bool.and_eq_true] at he
      obtain ⟨o, s1, h1, h2⟩ := bind_ok h
      have hs := ih.expr _ _ _ _ _ he.1 h1
      cases o with
      | none => cases hs
      | some v =>
        obtain ⟨o2, s2, h3, h4⟩ := bind_ok h2
        have hs2 := ih.args _ _ _ _ _ he.2 h3
        cases o2 with
        | none => cases hs2
        | some vs => cases pure_ok h4; rfl
  · -- evalBinds
    intro bs env s r s' he h
    cases bs with
    | nil => rw [evalBinds.eq_2] at h; cases pure_ok h; rfl
    | cons b bs =>
      obtain ⟨x, ty, e⟩ := b
      rw [evalBinds.eq_3] at h
      simp only [totalB, Bool.and_eq_true] at he
      obtain ⟨o, s1, h1, h2⟩ := bind_ok h
      have hs := ih.expr _ _ _ _ _ he.1 h1
      cases o with
      | none => cases hs
      | some v =>
        simp only at h2
        split at h2
        · exact ih.binds _ _ _ _ _ he.2 h2
        · exact (throw_ok h2).elim
  · -- applyTerm
    intro ty t vs s r s' htt h
    rw [applyTerm.eq_2] at h
    obtain ⟨term, s1, h1, h2⟩ := bind_ok h
    obtain ⟨_, ht, he⟩ := liftM_ok h1
    cases he
    unfold termTotal at htt
    rw [ht] at htt
    simp only at htt
    cases hk : term.kind with
    | enumVariant k => rw [hk] at h2; cases pure_ok h2; rfl
    | struct => rw [hk] at h2; cases pure_ok h2; rfl
    | decl flags ctor ex =>
      rw [hk] at htt h2
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at htt
      cases ctor with
      | none => exact (throw_ok h2).elim
      | some c =>
        cases c with
        | external fn =>
          simp only at h2
          split at h2
          · exact (throw_ok h2).elim
          · obtain ⟨g, s2, h3, h4⟩ := bind_ok h2
            cases get_ok h3
            simp only at h4
            split at h4
            · obtain ⟨u, s3, h5, h6⟩ := bind_ok h4
              cases pure_ok h6; rfl
            · simp only [htt, Bool.false_eq_true, ↓reduceIte] at h4
              exact (throw_ok h4).elim
            · exact (throw_ok h4).elim
        | internal =>
          simp only at h2
          split at h2
          · exact (throw_ok h2).elim
          · obtain ⟨sel, s2, h3, h4⟩ := bind_ok h2
            cases sel with
            | none =>
              simp only [htt, Bool.false_eq_true, ↓reduceIte] at h4
              exact (throw_ok h4).elim
            | some re =>
              obtain ⟨rl, env⟩ := re
              have hrhs := totalE_rhs p htp ht hk htt (selectRule_mem p sm cfg h3)
              obtain ⟨ev, s3, h5, h6⟩ := bind_ok h4
              have hs := ih.expr _ _ _ _ _ hrhs h5
              cases ev with
              | none => cases hs
              | some v =>
                obtain ⟨u, s4, h7, h8⟩ := bind_ok h6
                cases pure_ok h8; rfl

end Generic

/-- The exported program: every rule of a non-`partial` internal term has a total right-hand
side. -/
theorem totalProg_program : totalProg program = true := by native_decide

/-- **Totality** of the exported program, for every embedding context and configuration. -/
theorem totality : Totality :=
  ⟨fun ctx cfg n _ _ _ _ _ he h =>
    (totAt program (sem ctx) cfg totalProg_program n).expr _ _ _ _ _ he h,
   fun ctx cfg n _ _ _ _ _ _ ht h =>
    (totAt program (sem ctx) cfg totalProg_program n).apply _ _ _ _ _ _ ht h⟩

end Backend.Proof.Cov
