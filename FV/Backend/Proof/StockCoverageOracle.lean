import FV.Backend.Proof.StockSourceView
import FV.Backend.Proof.IselCovModel

/-! The existing operand-size oracle runs on actual Stock state without
changing it. Reuses IselCovModel's two-rule argument and source-pattern transport. -/
namespace Backend.Stock.Proof.Coverage
open Backend Backend.Proof Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
variable {f : Clif.Function} {ctx : Ctx} {cfg : Config}

/-- A match of a rule without if-lets keeps the state and is its argument match. -/
private theorem matchRule_noIfLets {m : Nat} {r : Rule} (hr : r.iflets = []) {vs : List V}
    {s s1 : State × Array RuleId} {o : Option (Isle.Interp.Env V)}
    (h : (matchRule program (Stock.sem ctx) cfg m r vs).run s = .ok (o, s1)) :
    s1 = s ∧ matchArgs program (Stock.sem ctx) s.1 r.args vs (Array.replicate r.vars.length none) = .ok o := by
  rcases m with _ | m
  · rw [matchRule.eq_1] at h; cases h
  rw [matchRule.eq_2] at h
  simp only [M.run_bind, M.run_get, M.except_ok_bind] at h
  cases ha : matchArgs program (Stock.sem ctx) s.1 r.args vs (Array.replicate r.vars.length none) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    rw [ha] at h
    simp only [isel_monad] at h
    cases q with
    | none =>
      simp only [isel_monad, Except.ok.injEq, Prod.mk.injEq] at h
      exact ⟨h.2.symm, by rw [h.1]⟩
    | some env =>
      simp only [hr] at h
      rcases m with _ | m
      · rw [matchIfLets.eq_1] at h; cases h
      · rw [matchIfLets.eq_2] at h
        simp only [isel_monad, Except.ok.injEq, Prod.mk.injEq] at h
        exact ⟨h.2.symm, by rw [h.1]⟩

/-- The right-hand sides of `operand_size`'s rules: an enum constant, the state unchanged. -/
private theorem os_rhs {n : Nat} {r : Rule} (hr : r ∈ program.rulesOf 305) {env : Isle.Interp.Env V}
    {s s' : State × Array RuleId} {o : Option V}
    (h : (evalExpr program (Stock.sem ctx) cfg n r.rhs env).run s = .ok (o, s')) :
    s' = s ∧ ((r = rule_inst_1592 ∧ o = some (.data 93 0 [])) ∨
      (r = rule_inst_1593 ∧ o = some (.data 93 1 []))) := by
  rw [program_rulesOf_305] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl <;> rcases n with _ | _ | n
  all_goals first
    | (rw [evalExpr.eq_1] at h; cases h)
    | skip
  all_goals simp only [rule_inst_1592, rule_inst_1593, evalExpr.eq_7, evalArgs.eq_1, evalArgs.eq_2,
      applyTerm.eq_2, program_term_2028, program_term_2029, term_2028_kind, term_2029_kind,
      isel_monad, isel_data] at h
  all_goals cases h
  all_goals simp [Stock.sem, Backend.sem]

private theorem rule_1592_ne_1593 : rule_inst_1592 ≠ rule_inst_1593 := fun h => by
  have := congrArg Rule.id h
  simp [rule_inst_1592, rule_inst_1593] at this

/-- **`operand_size` at every fuel**: a run that does not throw keeps the lowering state and
returns `Size32` (first rule: the argument type fits in 32 bits) or `Size64` (second rule: it
does not, and fits in 64 bits). -/
private theorem os_run (hc : cfg.checkOverlap = false) {n : Nat} {ty : TypeId} {vs : List V}
    {s s' : State × Array RuleId} {o : Option V}
    (h : (applyTerm program (Stock.sem ctx) cfg n ty 305 vs).run s = .ok (o, s')) :
    s'.1 = s.1 ∧ ∃ v, o = some v ∧
      ((v = .data 93 0 [] ∧ ∀ t, vs = [.ty t] → t.bits ≤ 32) ∨
        (v = .data 93 1 [] ∧ ∀ t, vs = [.ty t] → ¬ t.bits ≤ 32 ∧ t.bits ≤ 64)) := by
  rcases n with _ | n
  · rw [applyTerm.eq_1] at h; cases h
  cases o with
  | none =>
    exfalso
    rw [applyTerm_internal_run program_term_305 term_305_kind rfl] at h
    cases hs : (selectRule program (Stock.sem ctx) cfg n T.«operand_size» (program.rulesOf 305) vs).run s with
    | error e => rw [hs] at h; cases h
    | ok q =>
      obtain ⟨sel, s1⟩ := q
      rw [hs] at h
      simp only [isel_monad] at h
      cases sel with
      | none => simp [isel_monad] at h
      | some re =>
        obtain ⟨r, env⟩ := re
        obtain ⟨hr, -⟩ := selectRule_some hc hs
        simp only [isel_monad] at h
        cases he : (evalExpr program (Stock.sem ctx) cfg n r.rhs env).run s1 with
        | error e => rw [he] at h; cases h
        | ok q =>
          obtain ⟨ev, st⟩ := q
          rw [he] at h
          obtain ⟨-, hv⟩ := os_rhs hr he
          rcases hv with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
            simp only [isel_monad, M.run_fire_pure, Except.ok.injEq, Prod.mk.injEq, reduceCtorEq,
              false_and] at h
  | some v =>
    obtain ⟨r, pre, post, hrs, hpre, m, env, s1, st, tr, -, hmatch, he, rfl⟩ :=
      applyTerm_internal_some_first hc program_term_305 term_305_kind rfl h
    have hr : r ∈ program.rulesOf 305 := by rw [hrs]; simp
    obtain ⟨hst, hv⟩ := os_rhs hr he
    cases hst
    rw [program_rulesOf_305] at hrs
    rcases hv with ⟨rfl, hv⟩ | ⟨rfl, hv⟩ <;> obtain rfl := Option.some.inj hv
    · obtain ⟨rfl, hma⟩ := matchRule_noIfLets rfl hmatch
      refine ⟨rfl, _, rfl, .inl ⟨rfl, fun t ht => ?_⟩⟩
      subst ht
      rw [stock_matchArgs] at hma
      isel_inv_simp [rule_inst_1592, program_term_111, Cov.sem_extract] at hma
      obtain ⟨w, ws, ⟨rfl, -⟩, env1, ⟨fs, hf, -⟩, -⟩ := hma
      rw [ext_fits_in_32_iff] at hf
      exact hf.1
    · have h92 : rule_inst_1592 ∈ pre := by
        rcases pre with _ | ⟨a, pre⟩
        · simp only [List.nil_append, List.cons.injEq] at hrs
          exact absurd hrs.1 rule_1592_ne_1593
        · simp only [List.cons_append, List.cons.injEq] at hrs
          simp [hrs.1]
      obtain ⟨rfl, hma⟩ := matchRule_noIfLets rfl hmatch
      refine ⟨rfl, _, rfl, .inr ⟨rfl, fun t ht => ?_⟩⟩
      subst ht
      obtain ⟨m', -, s2, h2⟩ := hpre _ h92
      obtain ⟨-, h2⟩ := matchRule_noIfLets rfl h2
      rw [stock_matchArgs] at h2
      rw [stock_matchArgs] at hma
      isel_inv_simp [rule_inst_1593, program_term_113, Cov.sem_extract] at hma
      obtain ⟨w, ws, ⟨rfl, -⟩, env1, ⟨fs, hf, -⟩, -⟩ := hma
      rw [ext_fits_in_64_iff] at hf
      refine ⟨fun h32 => ?_, hf.1⟩
      revert h2
      isel_eval [rule_inst_1592, ext_fits_in_32', h32, program_term_111, Cov.sem_extract, stock_matchArgs]
      simp

/-! ## The oracle and the model -/

private theorem γ_os {k : Nat} : γ f (sourceIdentityCtx ctx) .c0 (.data 93 k []) :=
  ⟨fun r hr => by simp [V.regsIn, Backend.Proof.Flow.regsInL] at hr, fun _ => rfl⟩

/-- **The `operand_size` oracle is sound at every fuel**: the run keeps the lowering state and its
result is described by `aOracle`'s answer. -/
theorem oracle_sound (I : State → Prop) (cfg : Config) (hc : cfg.checkOverlap = false) (n : Nat)
    (ty : TypeId) (t : TermId) (as : List AW) (vs : List V) (a : AW) (s : State)
    (tr : Array RuleId) (r : Option V) (s' : State) (tr' : Array RuleId)
    (ha : aOracle t as = some a) (hvs : Holds2 f (sourceIdentityCtx ctx) as vs) (hIs : I s)
    (h : (applyTerm program (Stock.sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    I s' ∧ ∀ v, r = some v → γ f (sourceIdentityCtx ctx) a v := by
  unfold aOracle at ha
  split at ha
  case isFalse => cases ha
  rename_i ht
  have ht : t = 305 := eq_of_beq ht
  subst ht
  obtain ⟨hs, v0, rfl, hv0⟩ := os_run hc h
  cases hs
  refine ⟨hIs, fun v hv => ?_⟩
  cases hv
  split at ha
  · rename_i t1
    cases ha
    rcases vs with _ | ⟨w, ws⟩
    · exact absurd hvs id
    have hw : γ f (sourceIdentityCtx ctx) (.ty [t1]) w ∧ γL f (sourceIdentityCtx ctx) [] ws := hvs
    obtain rfl : ws = [] := by
      cases ws with
      | nil => rfl
      | cons _ _ => exact absurd hw.2 id
    obtain ⟨t', ht', rfl⟩ := hw.1
    obtain rfl := List.mem_singleton.mp ht'
    rcases hv0 with ⟨rfl, h32⟩ | ⟨rfl, h64⟩
    · simp only [h32 _ rfl, ↓reduceIte]
      exact ⟨[], rfl, trivial⟩
    · obtain ⟨hn, hb⟩ := h64 _ rfl
      simp only [hn, hb, ↓reduceIte]
      exact ⟨[], rfl, trivial⟩
  · cases ha
    rcases hv0 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> exact γ_os


end Backend.Stock.Proof.Coverage
