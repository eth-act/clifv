import FV.Backend.Proof.IselCmpBase

/-!
# Contracts of the small helper terms of the compare family

Each lemma: an internal constructor call that returned a value (`ApplyInternal`) returned
exactly this value and left the lowering state unchanged (only the trace grew). Proved by
inverse evaluation over every rule of the term (`applyTerm_internal_some`, `isel_inv`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

variable {p : Program} (hp : Data p) {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)

include hc in
/-- Split an internal-term call into its rules: the rule that fired, matched with fuel
`m' + 20` and evaluated with fuel `n' + 20`. -/
theorem internal_split {ty : TypeId} {t : TermId} {vs : List V} {term : Term} {flags : TermFlags}
    {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n ty t vs s v s') :
    ∃ r ∈ p.rulesOf t, ∃ m' n' env s1 st tr,
      (matchRule p (sem ctx) cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p (sem ctx) cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) := by
  obtain ⟨r, hr, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ := applyTerm_internal_some hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  exact ⟨r, hr, m', n', env, s1, st, tr, hmt, he, rfl⟩

include hc in
/-- `internal_split` with first-match selection: the rules before the committed one failed to
match (from the same start state). -/
theorem internal_split_first {ty : TypeId} {t : TermId} {vs : List V} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} (ht : termOf p t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex) (hm : flags.isMulti = false)
    {n : Nat} (hn : 22 + (p.rulesOf t).length ≤ n) {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n ty t vs s v s') :
    ∃ pre r post, p.rulesOf t = pre ++ r :: post ∧
      (∀ r' ∈ pre, ∃ m' s1, (matchRule p (sem ctx) cfg (m' + 20) r' vs).run s = .ok (none, s1)) ∧
      ∃ m' n' env s1 st tr,
      (matchRule p (sem ctx) cfg (m' + 20) r vs).run s = .ok (some env, s1) ∧
      (evalExpr p (sem ctx) cfg (n' + 20) r.rhs env).run s1 = .ok (some v, (st, tr)) ∧
      s' = (st, tr.push r.id) := by
  obtain ⟨r, pre, post, hL, hpre, m, env, s1, st, tr, hmn, hmt, he, rfl⟩ :=
    applyTerm_internal_some_first hc ht hk hm h
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 20 := ⟨m - 20, by omega⟩
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 20 := ⟨n - 20, by omega⟩
  refine ⟨pre, r, post, hL, fun r' hr' => ?_, m', n', env, s1, st, tr, hmt, he, rfl⟩
  obtain ⟨k, hk, s2, h2⟩ := hpre r' hr'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 20 := ⟨k - 20, by omega⟩
  exact ⟨k', s2, h2⟩

/-! ## `operand_size` -/

include hp hc in
theorem operand_size_ok {n : Nat} (hn : 30 ≤ n) {t : CTy} {s s' : LState × Array RuleId} {v : V}
    (h : ApplyInternal p (sem ctx) cfg n 93 305 [.ty t] s v s') :
    s'.1 = s.1 ∧ ((t.bits ≤ 32 ∧ v = .data 93 0 []) ∨ (32 < t.bits ∧ t.bits ≤ 64 ∧ v = .data 93 1 [])) := by
  obtain ⟨pre, r, post, hL, hpre, m', n', env, s1, st, tr, hm, he, rfl⟩ :=
    internal_split_first hc hp.t305 term_305_kind rfl (by rw [hp.r305]; simp; omega) h
  rw [hp.r305] at hL
  isel_rule_cases hL
  all_goals cases hp
  · isel_inv [*, rule_inst_1592] at hm he
    exact .inl ‹_›
  · obtain ⟨k, s2, h2⟩ := hpre _ (List.mem_singleton_self _)
    isel_inv [*, rule_inst_1593] at hm he
    refine .inr ⟨Nat.lt_of_not_le fun h32 => ?_, ‹_›⟩
    revert h2
    isel_eval [*, rule_inst_1592, ext_fits_in_32', h32]
    simp

end Backend.Proof
