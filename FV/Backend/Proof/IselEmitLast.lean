import FV.Backend.Proof.IselEmitFns
import FV.Backend.Proof.IselEmitDefs
import FV.Backend.Proof.IselCovSound
import FV.Backend.Proof.IselShpOracle
import FV.Backend.Proof.IselShpTotal

/-!
# Emission conditions of the ISLE lowering (V6c): runs ending in a branch

For a model of the emission analysis (`CovModel aextE actorE apreE aOracle`, invariant
`EmSince s0`) and the emission check `emChk` sound for `MInst.ofV` (hypothesis `hchk`):

* `esr_last`: an `emit_side_effect` run on a side effect `senrLast` accepts emits its
  instructions, each `emitOk`, only the last with targets (rules 522/524/527 inverted at any
  fuel; `totality` excludes a `none` result);
* `aLast_sound`: a run of an expression `aLast` accepts ends with `EmLast s0` (`soundAt` for
  arguments, bindings and match phases; induction on the depth for internal-term calls);
* `root_last`: a root internal term whose rules pass `aRule`, `aRuleLast`, or never match.
-/

set_option maxRecDepth 20000

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

section Esr
variable {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
include hc

/-- A run of `emit_side_effect` that does not throw: one of its rules matched and its right-hand
side returned a value (`totality`), at some fuel. -/
theorem esr_rule {n : Nat} {ty : TypeId} {v : V} {s : LState} {tr : Array RuleId} {r : Option V}
    {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.emit_side_effect [v]).run (s, tr) =
      .ok (r, (s', tr'))) :
    ∃ rl ∈ program.rulesOf 242, ∃ k env w tr0,
      matchArgs program (sem ctx) s rl.args [v] (Array.replicate rl.vars.length none) =
        .ok (some env) ∧
      (evalExpr program (sem ctx) cfg k rl.rhs env).run (s, tr) = .ok (some w, (s', tr0)) := by
  have hs := totality.2 ctx cfg n ty 242 [v] (s, tr) r (s', tr') rfl h
  obtain ⟨w, rfl⟩ := Option.isSome_iff_exists.mp hs
  rcases n with _ | n
  · rw [applyTerm.eq_1] at h; cases h
  obtain ⟨rl, hrl, m, env, s1, st, tr0, -, hmt, he, hs'⟩ :=
    applyTerm_internal_some hc program_term_242 term_242_kind rfl h
  have hil : rl.iflets = [] := by
    rw [program_rulesOf_242] at hrl
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrl
    rcases hrl with rfl | rfl | rfl <;> rfl
  obtain ⟨rfl, hma⟩ := matchRule_noIfLets hil hmt
  simp only [Prod.mk.injEq] at hs'
  obtain ⟨rfl, -⟩ := hs'
  exact ⟨rl, hrl, n, env, w, tr0, hma, he⟩

set_option maxHeartbeats 4000000 in
theorem esr_inst {n : Nat} {ty : TypeId} {i : V} {s : LState} {tr : Array RuleId} {r : Option V}
    {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.emit_side_effect [.data 46 0 [i]]).run (s, tr) =
      .ok (r, (s', tr'))) :
    ∃ m, MInst.ofV i = some m ∧ s' = s.emit m := by
  obtain ⟨rl, hrl, k, env, w, tr0, hma, he⟩ := esr_rule hc h
  clear h
  rw [program_rulesOf_242] at hrl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrl
  rcases hrl with rfl | rfl | rfl <;>
  oracle_inv [rule_prelude_lower_522, rule_prelude_lower_524, rule_prelude_lower_527,
      program_term_1787, program_term_1788, program_term_1789] at hma he
  exact ⟨_, ‹_›, rfl⟩

set_option maxHeartbeats 4000000 in
theorem esr_inst2 {n : Nat} {ty : TypeId} {i j : V} {s : LState} {tr : Array RuleId}
    {r : Option V} {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.emit_side_effect [.data 46 1 [i, j]]).run
      (s, tr) = .ok (r, (s', tr'))) :
    ∃ m1 m2, MInst.ofV i = some m1 ∧ MInst.ofV j = some m2 ∧ s' = (s.emit m1).emit m2 := by
  obtain ⟨rl, hrl, k, env, w, tr0, hma, he⟩ := esr_rule hc h
  clear h
  rw [program_rulesOf_242] at hrl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrl
  rcases hrl with rfl | rfl | rfl <;>
  oracle_inv [rule_prelude_lower_522, rule_prelude_lower_524, rule_prelude_lower_527,
      program_term_1787, program_term_1788, program_term_1789] at hma he
  exact ⟨_, ‹_›, _, ‹_›, rfl⟩

set_option maxHeartbeats 4000000 in
theorem esr_inst3 {n : Nat} {ty : TypeId} {i j l : V} {s : LState} {tr : Array RuleId}
    {r : Option V} {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.emit_side_effect [.data 46 2 [i, j, l]]).run
      (s, tr) = .ok (r, (s', tr'))) :
    ∃ m1 m2 m3, MInst.ofV i = some m1 ∧ MInst.ofV j = some m2 ∧ MInst.ofV l = some m3 ∧
      s' = ((s.emit m1).emit m2).emit m3 := by
  obtain ⟨rl, hrl, k, env, w, tr0, hma, he⟩ := esr_rule hc h
  clear h
  rw [program_rulesOf_242] at hrl
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hrl
  rcases hrl with rfl | rfl | rfl <;>
  oracle_inv [rule_prelude_lower_522, rule_prelude_lower_524, rule_prelude_lower_527,
      program_term_1787, program_term_1788, program_term_1789] at hma he
  exact ⟨_, ‹_›, _, ‹_›, _, ‹_›, rfl⟩

end Esr

/-! ## Composition of the emission statements -/

section Comp
variable {s0 : LState}

theorem emSince_emLast {s : LState} (h : Driver.EmSince s0 s) : Driver.EmLast s0 s := by
  obtain ⟨ms, he, hok⟩ := h
  exact ⟨ms, he, fun m hm => (hok m hm).1,
    fun m hm => (hok m (List.dropLast_subset _ hm)).2⟩

theorem emSince_emLast_trans {s1 s2 : LState} (h1 : Driver.EmSince s0 s1)
    (h2 : Driver.EmLast s1 s2) : Driver.EmLast s0 s2 := by
  obtain ⟨ms1, he1, hok1⟩ := h1
  obtain ⟨ms2, he2, hok2, hl2⟩ := h2
  refine ⟨ms1 ++ ms2, by rw [he2, he1]; simp, fun m hm => ?_, fun m hm => ?_⟩
  · rcases List.mem_append.mp hm with hm | hm
    · exact (hok1 m hm).1
    · exact hok2 m hm
  · by_cases hne : ms2 = []
    · subst hne
      rw [List.append_nil] at hm
      exact (hok1 m (List.dropLast_subset _ hm)).2
    · rw [List.dropLast_append_of_ne_nil hne] at hm
      rcases List.mem_append.mp hm with hm | hm
      · exact (hok1 m hm).2
      · exact hl2 m hm

theorem emLast_of_list {s s' : LState} (ms : List MInst)
    (he : s'.emitted = s.emitted ++ ms.toArray) (hok : ∀ m ∈ ms, m.emitOk = true)
    (hl : ∀ m ∈ ms.dropLast, m.targets = []) : Driver.EmLast s s' := ⟨ms, he, hok, hl⟩

end Comp

/-! ## The `emit_side_effect` tail -/

section Tail
variable {f : Clif.Function} {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false)
  (hchk : ∀ nb a v m, emChk nb a = true → γ f ctx a v → MInst.ofV v = some m →
    m.emitOk = true ∧ (nb = true → m.targets = []))
include hc hchk

/-- A side effect `senr1` checks: its `emit_side_effect` run emits its instructions, each
`emitOk`, all but the last without targets. -/
theorem esr1_last {a : AW} {v : V} (ha : senr1 a = true) (hv : γ f ctx a v) {n : Nat} {ty : TypeId}
    {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.emit_side_effect [v]).run (s, tr) =
      .ok (r, (s', tr'))) : Driver.EmLast s s' := by
  unfold senr1 at ha
  split at ha
  · rename_i t k i
    simp only [Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨rfl, rfl⟩, hi⟩ := ha
    obtain ⟨vs, rfl, hl⟩ := hv
    match vs, hl with
    | [vi], ⟨hvi, _⟩ =>
      obtain ⟨m, hm, rfl⟩ := esr_inst hc h
      have hok := hchk _ _ _ _ hi hvi hm
      exact emLast_of_list [m] (by simp [LState.emit])
        (by simpa using hok.1) (by simp)
  · rename_i t k i j
    simp only [Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨⟨rfl, rfl⟩, hi⟩, hj⟩ := ha
    obtain ⟨vs, rfl, hl⟩ := hv
    match vs, hl with
    | [vi, vj], ⟨hvi, hvj, _⟩ =>
      obtain ⟨m1, m2, hm1, hm2, rfl⟩ := esr_inst2 hc h
      have hok1 := hchk _ _ _ _ hi hvi hm1
      have hok2 := hchk _ _ _ _ hj hvj hm2
      exact emLast_of_list [m1, m2]
        (by simp only [LState.emit, Array.push_eq_append, Array.append_assoc] <;> rfl)
        (by simp [hok1.1, hok2.1]) (by simp [hok1.2 rfl])
  · rename_i t k i j l
    simp only [Bool.and_eq_true, beq_iff_eq] at ha
    obtain ⟨⟨⟨⟨rfl, rfl⟩, hi⟩, hj⟩, hl'⟩ := ha
    obtain ⟨vs, rfl, hl⟩ := hv
    match vs, hl with
    | [vi, vj, vl], ⟨hvi, hvj, hvl, _⟩ =>
      obtain ⟨m1, m2, m3, hm1, hm2, hm3, rfl⟩ := esr_inst3 hc h
      have hok1 := hchk _ _ _ _ hi hvi hm1
      have hok2 := hchk _ _ _ _ hj hvj hm2
      have hok3 := hchk _ _ _ _ hl' hvl hm3
      exact emLast_of_list [m1, m2, m3]
        (by simp only [LState.emit, Array.push_eq_append, Array.append_assoc] <;> rfl)
        (by simp [hok1.1, hok2.1, hok3.1]) (by simp [hok1.2 rfl, hok2.2 rfl])
  · cases ha

/-- `senrLast`: every alternative checks. -/
theorem esr_last {a : AW} {v : V} (ha : senrLast a = true) (hv : γ f ctx a v) {n : Nat}
    {ty : TypeId} {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState}
    {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty TId.emit_side_effect [v]).run (s, tr) =
      .ok (r, (s', tr'))) : Driver.EmLast s s' := by
  cases a with
  | alts as =>
    obtain ⟨x, hx, hxv⟩ := γAny_iff.mp hv
    exact esr1_last hc hchk (List.all_eq_true.mp ha x hx) hxv h
  | _ => exact esr1_last hc hchk (by unfold senrLast at ha; exact ha) hv h

end Tail

/-! ## Internal terms -/

section Apply
variable {ctx : Ctx} {cfg : Config} (hc : cfg.checkOverlap = false) {s0 : LState}
include hc

/-- A run of an internal term from a state with `EmSince s0`: `EmLast s0` if every matching
rule's right-hand side, run from its match, gives `EmLast s0`. -/
theorem apply_internal_last {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    (ht : termOf program t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    {vs : List V} {s : LState} {tr : Array RuleId} (hs : Driver.EmSince s0 s)
    (hrule : ∀ rl ∈ program.rulesOf t, ∀ (m : Nat) (env : Isle.Interp.Env V) (s1 : LState)
      (tr1 : Array RuleId) (k : Nat) (o : Option V) (s2 : LState) (tr2 : Array RuleId),
      (matchRule program (sem ctx) cfg m rl vs).run (s, tr) = .ok (some env, (s1, tr1)) →
      (evalExpr program (sem ctx) cfg k rl.rhs env).run (s1, tr1) = .ok (o, (s2, tr2)) →
      Driver.EmLast s0 s2)
    {n : Nat} {ty : TypeId} {r : Option V} {s' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    Driver.EmLast s0 s' := by
  rcases n with _ | n
  · rw [applyTerm.eq_1] at h; exact (throw_ok h).elim
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
    · cases pure_ok h2; exact emSince_emLast hs
    · exact (throw_ok h2).elim
  | some re =>
    obtain ⟨rl, env⟩ := re
    obtain ⟨hrl, m, -, hmatch⟩ := selectRule_some_lt hc h1
    simp only at h2
    obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    have hl := hrule rl hrl m env s1 tr1 n ev s2 tr2 hmatch h3
    cases ev with
    | some v =>
      obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
      have hf := fire_ok h5
      cases pure_ok h6
      simp only at hf
      subst hf
      exact hl
    | none => cases pure_ok h4; exact hl

end Apply

/-! ## Soundness of `aLast` -/

section Sound
variable {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {s0 : LState}
  (md : CovModel aextE actorE apreE aOracle program f ctx)
  (hmd : ∀ s, md.Is s ↔ Driver.EmSince s0 s) {cfg : Config} (hc : cfg.checkOverlap = false)
  {tab : Tab} (htab : chkTab program tab aextE actorE apreE aOracle = true)
  (hchk : ∀ nb a v m, emChk nb a = true → γ f ctx a v → MInst.ofV v = some m →
    m.emitOk = true ∧ (nb = true → m.targets = []))
include hctx hmd hc htab hchk

/-- **Soundness of `aLast`**: a run of an expression `aLast` accepts, from a state with
`EmSince s0`, ends in a state with `EmLast s0`. -/
theorem aLast_sound : ∀ (k : Nat) (e : Isle.Expr) (aenv : List AW) (env : Isle.Interp.Env V)
    (n : Nat) (s : LState) (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId),
    aLast program tab aextE actorE apreE aOracle k e aenv = true → EnvOK f ctx aenv env →
    Driver.EmSince s0 s →
    (evalExpr program (sem ctx) cfg n e env).run (s, tr) = .ok (r, (s', tr')) →
    Driver.EmLast s0 s' := by
  have sa := soundAt hctx md cfg tab hc htab
  intro k
  induction k with
  | zero => intro e aenv env n s tr r s' tr' ha; simp [aLast] at ha
  | succ k ih =>
  intro e aenv env n s tr r s' tr' ha he hs h
  rcases n with _ | n
  · rw [evalExpr.eq_1] at h; exact (throw_ok h).elim
  cases e with
  | term ty t args =>
    rw [evalExpr.eq_7] at h
    obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
    simp only [aLast] at ha
    split at ha
    · rename_i hte
      obtain rfl : t = TId.emit_side_effect := eq_of_beq hte
      split at ha
      · rename_i e
        split at ha
        · rename_i a hae
          obtain ⟨hIs1, hv1⟩ := (sa n).args [e] aenv [a] env s tr o s1 tr1
            (by simp [aArgs, hae]) he ((hmd s).2 hs) h1
          have hs1 := (hmd s1).1 hIs1
          cases o with
          | none => cases pure_ok h2; exact emSince_emLast hs1
          | some vs =>
            match vs, hv1 vs rfl with
            | [v], ⟨hv, _⟩ => exact emSince_emLast_trans hs1 (esr_last hc hchk ha hv h2)
        · cases ha
      · cases ha
    · simp only [Bool.and_eq_true] at ha
      obtain ⟨⟨hio, -⟩, ha⟩ := ha
      split at ha
      · rename_i as hargs
        obtain ⟨hIs1, hv1⟩ := (sa n).args args aenv as env s tr o s1 tr1 hargs he ((hmd s).2 hs) h1
        have hs1 := (hmd s1).1 hIs1
        cases o with
        | none => cases pure_ok h2; exact emSince_emLast hs1
        | some vs =>
          unfold internalOne at hio
          split at hio
          · rename_i term htm
            split at hio
            · rename_i flags ex hk
              refine apply_internal_last hc htm hk hs1 ?_ h2
              intro rl hrl m env' s2 tr2 k' o' s3 tr3 hmatch hrhs
              have hr := List.all_eq_true.mp ha rl hrl
              split at hr
              · rename_i envs hae
                obtain ⟨hIs2, aenv', haenv, he'⟩ :=
                  (sa m).mrule _ _ _ _ _ _ _ _ _ hae (hv1 vs rfl) hIs1 hmatch
                exact ih rl.rhs aenv' env' k' s2 tr2 o' s3 tr3 (List.all_eq_true.mp hr aenv' haenv)
                  he' ((hmd s2).1 hIs2) hrhs
              · cases hr
            · cases hio
          · cases hio
      · cases ha
  | «let» ty bs body =>
    rw [evalExpr.eq_6] at h
    simp only [aLast] at ha
    split at ha
    · rename_i aenv' hb
      obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨hIs1, he1⟩ := (sa n).binds _ _ _ _ _ _ _ _ _ hb he ((hmd s).2 hs) h1
      cases o with
      | none => cases pure_ok h2; exact emSince_emLast ((hmd _).1 hIs1)
      | some env' =>
        exact ih body aenv' env' n s1 tr1 r s' tr' ha (he1 env' rfl) ((hmd s1).1 hIs1) h2
    · cases ha
  | _ => simp [aLast] at ha

/-- **A root term whose rules pass `aRule`, end in a branch (`aRuleLast`), or never match**: a
run from a state with `EmSince s0` ends in a state with `EmLast s0`. -/
theorem root_last {vs : List V} {K : Nat} {ty : TypeId} {t : TermId} {term : Term}
    {flags : TermFlags} {ex : Option Extractor} {ins : List AW} {s : LState} {tr : Array RuleId}
    {r : Option V} {s' : LState} {tr' : Array RuleId} (ht : termOf program t = .ok term)
    (hk : term.kind = .decl flags (some .internal) ex)
    (hrules : ∀ rl ∈ program.rulesOf t,
      aRule program tab aextE actorE apreE aOracle ins AW.top rl = true ∨
      aRuleLast program tab aextE actorE apreE aOracle K ins rl = true ∨
      (∀ m st env s1, (matchRule program (sem ctx) cfg m rl vs).run st ≠ .ok (some env, s1)))
    (hins : Holds2 f ctx ins vs) (hs : Driver.EmSince s0 s) {n : Nat}
    (h : (applyTerm program (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    Driver.EmLast s0 s' := by
  have sa := soundAt hctx md cfg tab hc htab
  refine apply_internal_last hc ht hk hs ?_ h
  intro rl hrl m env s1 tr1 k o s2 tr2 hmatch hrhs
  rcases hrules rl hrl with hok | hlast | hno
  · obtain ⟨envs, hae, hall⟩ := aRule_inv hok
    obtain ⟨hIs1, aenv, haenv, he1⟩ :=
      (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins ((hmd s).2 hs) hmatch
    obtain ⟨a, ha, -⟩ := hall aenv haenv
    exact emSince_emLast ((hmd s2).1 ((sa k).expr _ _ _ _ _ _ _ _ _ ha he1 hIs1 hrhs).1)
  · unfold aRuleLast at hlast
    split at hlast
    · rename_i envs hae
      obtain ⟨hIs1, aenv, haenv, he1⟩ :=
        (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins ((hmd s).2 hs) hmatch
      exact aLast_sound hctx md hmd hc htab hchk K rl.rhs aenv env k s1 tr1 o s2 tr2
        (List.all_eq_true.mp hlast aenv haenv) he1 ((hmd s1).1 hIs1) hrhs
    · cases hlast
  · exact absurd hmatch (hno m _ _ _)

end Sound

end Backend.Proof.Cov
