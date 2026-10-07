import FV.Backend.Proof.IselCovSound
import FV.Backend.Proof.IselGeneric

/-!
# Control shapes of the ISLE lowering (V4): root terms with hand-checked rules

`root_hand`: `SoundAt.root` where a rule may also be checked by hand (`Hand rl`: its match and
right-hand side keep the model's invariant, at a large fuel). Only the invariant is concluded.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx} {p : Program} {aext : TermId → AW → List AW}
  {actor : TermId → List AW → AW}
  {apre : TermId → List AW → Bool} {aOracle : TermId → List AW → Option AW}
  {md : CovModel aext actor apre aOracle p f ctx} {cfg : Config} {tab : Tab}

/-- **A root term whose rules pass `aRule`, never match, or are checked by hand** keeps the
invariant (at a fuel leaving every hand-checked match and right-hand side 1000 steps). -/
theorem root_hand (hc : cfg.checkOverlap = false) (sa : ∀ n, SoundAt md cfg tab n)
    {vs : List V} {Hand : Rule → Prop}
    (hhand : ∀ rl, Hand rl → ∀ (m n : Nat) (s : LState) (tr : Array RuleId) (env : Isle.Interp.Env V)
      (s1 : LState × Array RuleId) (r : Option V) (s2 : LState) (tr2 : Array RuleId),
      1000 ≤ m → 1000 ≤ n → md.Is s →
      (matchRule p (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, s1) →
      (evalExpr p (sem ctx) cfg n rl.rhs env).run s1 = .ok (r, (s2, tr2)) → md.Is s2)
    {ty : TypeId} {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    {ins : List AW} {out : AW} {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState}
    {tr' : Array RuleId} (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hrules : ∀ rl ∈ p.rulesOf t, aRule p tab aext actor apre aOracle ins out rl = true ∨
      (∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) ∨ Hand rl)
    (hins : Holds2 f ctx ins vs) (hIs : md.Is s) {n : Nat} (hn : 1002 + (p.rulesOf t).length ≤ n)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr'))) : md.Is s' := by
  cases hm : flags.isMulti with
  | true =>
    rw [applyTerm.eq_2] at h
    obtain ⟨term', s1, h1, h2⟩ := bind_ok h
    obtain ⟨_, ht', he⟩ := liftM_ok h1
    rw [ht] at ht'; cases ht'; cases he
    rw [hk] at h2
    simp only [hm, ↓reduceIte] at h2
    exact (throw_ok h2).elim
  | false =>
  rw [applyTerm_internal_run ht hk hm] at h
  obtain ⟨⟨sel, ⟨s1, tr1⟩⟩, h1, h2⟩ := except_bind_eq_ok h
  cases sel with
  | none =>
    have := selectRule_none h1
    cases this
    simp only at h2
    split at h2
    · cases pure_ok h2; exact hIs
    · exact (throw_ok h2).elim
  | some re =>
    obtain ⟨rl, env⟩ := re
    obtain ⟨hrl, m, hmn, hmatch⟩ := selectRule_some_lt hc h1
    simp only at h2
    obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    have hfin : md.Is s2 → md.Is s' := by
      intro hIs2
      cases ev with
      | some v =>
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        have hf := fire_ok h5
        cases pure_ok h6
        simp only at hf
        subst hf
        exact hIs2
      | none => cases pure_ok h4; exact hIs2
    rcases hrules rl hrl with hok | hno | hhd
    · obtain ⟨envs, hae, hall⟩ := aRule_inv hok
      obtain ⟨hIs1, aenv, haenv, he1⟩ := (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins hIs hmatch
      obtain ⟨a, ha, -⟩ := hall aenv haenv
      exact hfin ((sa n).expr _ _ _ _ _ _ _ _ _ ha he1 hIs1 h3).1
    · exact absurd hmatch (hno m _ _ _)
    · obtain ⟨-, m', hm', hmatch'⟩ := selectRule_some hc h1
      exact hfin (hhand rl hhd m' n s tr env _ ev s2 tr2 (by omega) (by omega) hIs hmatch' h3)

end Backend.Proof.Cov
