import FV.Backend.Proof.IselSzDefs
import FV.Backend.Proof.IselCovSound
import FV.Backend.Proof.IselGeneric

/-!
# The size of the ISLE lowering's output (V6c): soundness of the cost analysis

For any measure `W` of the lowering state (the weight `wtA` or the branch targets `tgA` of the
emitted instructions), on top of the value soundness `SoundAt` of V3's abstract interpreter:
`costAt` (by induction on the fuel, mirroring `soundAt`) states that a run of an expression,
arguments, bindings, term application, rule match or if-lets grows `W` by at most the cost
`cExpr`/`cArgs`/`cBinds`/`cApply`/`cIfLets` (a rule's match: the maximum of `cIfLets` over the
environments of its argument patterns) gives, assuming the extern constructors' costs (`ExtW`),
the oracle's (`OracleW`) and the checked cost table (`chkCost`).

* A failed rule attempt restores the state (`selectRule_none`, `selectRule_some_lt`); a
  committed rule costs its if-lets plus its right-hand side (`cRule`), and `fire` keeps the state.
* The abstract environments a match passes through come from `SoundAt` itself (`patArgs_env`,
  `pat_env`: the rule without its if-lets, a single if-let).
* `cost_root_hand`: a driver root whose rules pass `cRuleLe`, never match, or are checked by
  hand (`HandW`), grows `W` by at most the root's bound (`root_hand` for the cost).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

variable {f : Clif.Function} {ctx : Ctx} {p : Program} {aext : TermId → AW → List AW}
  {actor : TermId → List AW → AW}
  {apre : TermId → List AW → Bool} {aOracle : TermId → List AW → Option AW}
  {tab : Tab} {aw : TermId → List AW → Option Nat} {ctab : CTab}

/-! ## Maxima -/

theorem foldl_max_ge_init : ∀ (xs : List Nat) (b : Nat), b ≤ xs.foldl max b
  | [], _ => Nat.le_refl _
  | x :: xs, b => Nat.le_trans (Nat.le_max_left b x) (foldl_max_ge_init xs (max b x))

theorem le_foldl_max : ∀ {xs : List Nat} {x : Nat}, x ∈ xs → ∀ b, x ≤ xs.foldl max b
  | y :: ys, x, hx, b => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact Nat.le_trans (Nat.le_max_right b x) (foldl_max_ge_init ys _)
    · exact le_foldl_max hx _

/-! ## Inversion of the cost analysis -/

theorem cApply_aApply {ty : TypeId} {t : TermId} {as : List AW} {c : Nat}
    (h : cApply p tab aw ctab apre aOracle ty t as = some c) :
    ∃ a, aApply p tab actor apre aOracle ty t as = some a := by
  unfold cApply at h
  unfold aApply
  by_cases hb : as.any AW.isBot = true
  · simp [hb]
  rw [Bool.not_eq_true] at hb
  simp only [hb, Bool.false_eq_true, ↓reduceIte] at h ⊢
  cases ht : termOf p t with
  | error e => simp
  | ok term =>
    rw [ht] at h
    simp only at h ⊢
    split
    all_goals first
      | exact ⟨_, rfl⟩
      | (rename_i hk; rw [hk] at h; simp only at h
         split at h
         · rename_i a ho; simp [ho]
         · rename_i ho
           simp only [ho]
           split at h
           · rename_i out htab; exact ⟨out, htab⟩
           · cases h)
      | (rename_i hk; rw [hk] at h; simp only at h; split at h <;> simp_all)

/-- The cost analysis of an expression succeeds only where the abstract interpretation does. -/
theorem cExpr_aExpr : ∀ (e : Isle.Expr) (env : List AW) (c : Nat),
    cExpr p tab aw ctab actor apre aOracle e env = some c →
    ∃ a, aExpr p tab actor apre aOracle e env = some a
  | .var _ x, env, _, _ => ⟨_, by rw [aExpr]⟩
  | .constBool .., _, _, _ => ⟨_, by rw [aExpr]⟩
  | .constInt .., _, _, _ => ⟨_, by rw [aExpr]⟩
  | .constPrim .., _, _, _ => ⟨_, by rw [aExpr]⟩
  | .let ty bs body, env, c, h => by
    simp only [cExpr] at h
    split at h
    · rename_i env' c1 hb hc
      split at h
      · rename_i d hd
        obtain ⟨a, ha⟩ := cExpr_aExpr body env' d hd
        exact ⟨a, by simp only [aExpr, hb, ha]⟩
      · cases h
    · cases h
  | .term ty t args, env, c, h => by
    simp only [cExpr] at h
    split at h
    · rename_i as c1 has hc
      split at h
      · rename_i d hd
        obtain ⟨a, ha⟩ := cApply_aApply (actor := actor) hd
        exact ⟨a, by simp only [aExpr, has, ha]⟩
      · cases h
    · cases h

theorem cRuleLe_inv {ins : List AW} {c : Nat} {r : Rule}
    (h : cRuleLe p tab aw ctab aext actor apre aOracle ins c r = true) :
    ∃ cs envs ds, (aPatArgs p aext ins r.args (List.replicate r.vars.length .top)).mapM
        (cIfLets p tab aw ctab aext actor apre aOracle r.iflets) = some cs ∧
      aRuleEnvs p tab aext actor apre aOracle ins r = some envs ∧
      envs.mapM (cExpr p tab aw ctab actor apre aOracle r.rhs) = some ds ∧
      cs.foldl max 0 + ds.foldl max 0 ≤ c := by
  unfold cRuleLe at h
  split at h
  · rename_i c' hc'
    unfold cRule at hc'
    split at hc'
    · rename_i cs envs h1 h2
      split at hc'
      · rename_i ds h3
        cases hc'
        exact ⟨cs, envs, ds, h1, h2, h3, of_decide_eq_true h⟩
      · cases hc'
    · cases hc'
  · cases h

theorem ctabGet_le {t : TermId} {as : List AW} {c : Nat} (h : ctabGet ctab t as = some c) :
    ∃ ins, (t, ins, c) ∈ ctab ∧ AW.leAll as ins = true := by
  unfold ctabGet at h
  cases hf : ctab.find? (fun e => e.1 == t && AW.leAll as e.2.1) with
  | none => rw [hf] at h; cases h
  | some e =>
    rw [hf] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have hm := List.mem_of_find?_eq_some hf
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨e.2.1, by rw [← hp.1]; exact hm, hp.2⟩

theorem chkCost_mem (hc : chkCost p tab aw ctab aext actor apre aOracle = true) {t : TermId}
    {ins : List AW} {c : Nat} (hm : (t, ins, c) ∈ ctab) :
    ∀ r ∈ p.rulesOf t, cRuleLe p tab aw ctab aext actor apre aOracle ins c r = true := by
  have := List.all_eq_true.mp hc _ hm
  exact List.all_eq_true.mp this

theorem mapM_single_flatten : ∀ (xs : List (List AW)),
    (xs.mapM fun e => (some [e] : Option (List (List AW)))).map List.flatten = some xs
  | [] => rfl
  | x :: xs => by
    have := mapM_single_flatten xs
    cases hm : xs.mapM fun e => (some [e] : Option (List (List AW))) with
    | none => rw [hm] at this; cases this
    | some ys =>
      rw [hm] at this
      simp only [Option.map_some, Option.some.injEq] at this
      simp [List.mapM_cons, hm, this]

/-! ## Environments of a match, from `SoundAt` -/

section Env
variable {md : CovModel aext actor apre aOracle p f ctx} {cfg : Config}

/-- The environment after a rule's argument patterns is described by one of `aPatArgs`'s
(`SoundAt.mrule` for the rule without its if-lets). -/
theorem patArgs_env (sa : ∀ n, SoundAt md cfg tab n) {rl : Rule} {ins : List AW} {vs : List V}
    {s : LState} {env0 : Isle.Interp.Env V} (hins : Holds2 f ctx ins vs) (hIs : md.Is s)
    (hma : matchArgs p (sem ctx) s rl.args vs (Array.replicate rl.vars.length none) =
      .ok (some env0)) :
    ∃ aenv0 ∈ aPatArgs p aext ins rl.args (List.replicate rl.vars.length .top),
      EnvOK f ctx aenv0 env0 := by
  let rl' : Rule := { rl with iflets := [] }
  have hae : aRuleEnvs p tab aext actor apre aOracle ins rl' =
      some (aPatArgs p aext ins rl.args (List.replicate rl.vars.length .top)) := by
    unfold aRuleEnvs
    simp only [rl', aIfLets.eq_1]
    exact mapM_single_flatten _
  have hrun : (matchRule p (sem ctx) cfg 2 rl' vs).run (s, #[]) = .ok (some env0, (s, #[])) := by
    rw [matchRule.eq_2]
    simp [rl', hma, matchIfLets.eq_2]
  exact ((sa 2).mrule rl' ins _ vs s #[] env0 s #[] hae hins hIs hrun).2

/-- The environment after an if-let's pattern is described by one of `aPat`'s (`SoundAt.iflets`
for that if-let alone). -/
theorem pat_env (sa : ∀ n, SoundAt md cfg tab n) {il : IfLet} {a : AW} {aenv : List AW}
    {env env1 : Isle.Interp.Env V} {v : V} {s s1 : LState} {tr tr1 : Array RuleId} {k : Nat}
    (ha : aExpr p tab actor apre aOracle il.rhs aenv = some a) (he : EnvOK f ctx aenv env)
    (hIs : md.Is s)
    (hrun : (evalExpr p (sem ctx) cfg (k + 1) il.rhs env).run (s, tr) = .ok (some v, (s1, tr1)))
    (hmp : matchPat p (sem ctx) s1 il.lhs v env = .ok (some env1)) :
    ∃ aenv1 ∈ aPat p aext a il.lhs aenv, EnvOK f ctx aenv1 env1 := by
  have hif : aIfLets p tab aext actor apre aOracle [il] aenv = some (aPat p aext a il.lhs aenv) := by
    rw [aIfLets.eq_2, ha]
    simp only [aIfLets.eq_1]
    exact mapM_single_flatten _
  have hr : (matchIfLets p (sem ctx) cfg (k + 2) [il] env).run (s, tr) =
      .ok (some env1, (s1, tr1)) := by
    rw [matchIfLets.eq_3]
    simp [hrun, hmp, matchIfLets.eq_2]
  exact ((sa (k + 2)).iflets _ _ _ _ _ _ _ _ _ hif he hIs hr).2

end Env

/-! ## Soundness of the cost analysis -/

section Cost
variable (md : CovModel aext actor apre aOracle p f ctx) (cfg : Config) (tab : Tab)
  (aw : TermId → List AW → Option Nat) (ctab : CTab) (W : LState → Nat)

/-- The cost statements at fuel `n`: a run grows the measure `W` by at most the cost. -/
structure CostAt (n : Nat) : Prop where
  expr : ∀ e aenv c env s tr r s' tr', cExpr p tab aw ctab actor apre aOracle e aenv = some c →
    EnvOK f ctx aenv env → md.Is s →
    (evalExpr p (sem ctx) cfg n e env).run (s, tr) = .ok (r, (s', tr')) → W s' ≤ W s + c
  args : ∀ es aenv c env s tr r s' tr', cArgs p tab aw ctab actor apre aOracle es aenv = some c →
    EnvOK f ctx aenv env → md.Is s →
    (evalArgs p (sem ctx) cfg n es env).run (s, tr) = .ok (r, (s', tr')) → W s' ≤ W s + c
  binds : ∀ bs aenv c env s tr r s' tr', cBinds p tab aw ctab actor apre aOracle bs aenv = some c →
    EnvOK f ctx aenv env → md.Is s →
    (evalBinds p (sem ctx) cfg n bs env).run (s, tr) = .ok (r, (s', tr')) → W s' ≤ W s + c
  apply : ∀ ty t as c vs s tr r s' tr', cApply p tab aw ctab apre aOracle ty t as = some c →
    Holds2 f ctx as vs → md.Is s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) → W s' ≤ W s + c
  root : ∀ ty t term flags ex ins c vs s tr r s' tr', termOf p t = .ok term →
    term.kind = .decl flags (some .internal) ex →
    (∀ rl ∈ p.rulesOf t, cRuleLe p tab aw ctab aext actor apre aOracle ins c rl = true ∨
      ∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
    Holds2 f ctx ins vs → md.Is s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) → W s' ≤ W s + c
  mrule : ∀ rl ins cs vs s tr env s' tr',
    (aPatArgs p aext ins rl.args (List.replicate rl.vars.length .top)).mapM
      (cIfLets p tab aw ctab aext actor apre aOracle rl.iflets) = some cs →
    Holds2 f ctx ins vs → md.Is s →
    (matchRule p (sem ctx) cfg n rl vs).run (s, tr) = .ok (some env, (s', tr')) →
    W s' ≤ W s + cs.foldl max 0
  iflets : ∀ ils aenv c env s tr env' s' tr',
    cIfLets p tab aw ctab aext actor apre aOracle ils aenv = some c →
    EnvOK f ctx aenv env → md.Is s →
    (matchIfLets p (sem ctx) cfg n ils env).run (s, tr) = .ok (some env', (s', tr')) →
    W s' ≤ W s + c

variable {md cfg tab aw ctab W}

/-- **Soundness of the cost analysis**, at every fuel: under the value soundness `sa`, the
extern constructors' costs (`ExtW`), the oracle's (`OracleW`) and the checked cost table
(`chkCost`), every run grows `W` by at most the cost the analysis gives. -/
theorem costAt (hc : cfg.checkOverlap = false) (sa : ∀ n, SoundAt md cfg tab n)
    (hext : ExtW f ctx apre aw W) (hor : OracleW p f ctx aOracle W)
    (hct : chkCost p tab aw ctab aext actor apre aOracle = true) :
    ∀ n, CostAt md cfg tab aw ctab W n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  cases n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rename_i h <;>
      first
      | (rw [evalExpr.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalArgs.eq_1] at h; exact (throw_ok h).elim)
      | (rw [evalBinds.eq_1] at h; exact (throw_ok h).elim)
      | (rw [applyTerm.eq_1] at h; exact (throw_ok h).elim)
      | (rw [matchRule.eq_1] at h; exact (throw_ok h).elim)
      | (rw [matchIfLets.eq_1] at h; exact (throw_ok h).elim)
  | succ n =>
  have ihn := ih n (Nat.lt_succ_self n)
  have hroot : ∀ ty t term flags ex ins c vs s tr r s' tr', termOf p t = .ok term →
      term.kind = .decl flags (some .internal) ex →
      (∀ rl ∈ p.rulesOf t, cRuleLe p tab aw ctab aext actor apre aOracle ins c rl = true ∨
        ∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) →
      Holds2 f ctx ins vs → md.Is s →
      (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr')) →
      W s' ≤ W s + c := by
    intro ty t term flags ex ins c vs s tr r s' tr' ht hk hrules hins hIs h
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
      · cases pure_ok h2; omega
      · exact (throw_ok h2).elim
    | some re =>
      obtain ⟨rl, env⟩ := re
      obtain ⟨hrl, m, hmn, hmatch⟩ := selectRule_some_lt hc h1
      have hok : cRuleLe p tab aw ctab aext actor apre aOracle ins c rl = true := by
        rcases hrules rl hrl with h | h
        · exact h
        · exact absurd hmatch (h m _ _ _)
      obtain ⟨cs, envs, ds, hcs, hae, hds, hle⟩ := cRuleLe_inv hok
      have hW1 := (ih m (by omega)).mrule _ _ _ _ _ _ _ _ _ hcs hins hIs hmatch
      obtain ⟨hIs1, aenv, haenv, he1⟩ := (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins hIs hmatch
      obtain ⟨d, hd, hcd⟩ := mapM_some_mem hds aenv haenv
      have hd' := le_foldl_max hd 0
      simp only at h2
      obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
      have hW2 := ihn.expr _ _ _ _ _ _ _ _ _ hcd he1 hIs1 h3
      cases ev with
      | some v =>
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        have hf := fire_ok h5
        cases pure_ok h6
        simp only at hf
        subst hf
        omega
      | none => cases pure_ok h4; omega
  refine ⟨?_, ?_, ?_, ?_, hroot, ?_, ?_⟩
  · -- evalExpr
    intro e aenv c env s tr r s' tr' hce he hIs h
    cases e with
    | var ty x =>
      rw [evalExpr.eq_2] at h
      split at h
      · cases pure_ok h; omega
      · exact (throw_ok h).elim
    | constBool ty b => rw [evalExpr.eq_3] at h; cases pure_ok h; omega
    | constInt ty i => rw [evalExpr.eq_4] at h; cases pure_ok h; omega
    | constPrim ty nm =>
      rw [evalExpr.eq_5] at h
      split at h
      · cases pure_ok h; omega
      · exact (throw_ok h).elim
    | «let» ty bs body =>
      rw [evalExpr.eq_6] at h
      simp only [cExpr] at hce
      split at hce
      · rename_i aenv' c1 hb hcb
        split at hce
        · rename_i d hd
          cases hce
          obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
          have hW1 := ihn.binds _ _ _ _ _ _ _ _ _ hcb he hIs h1
          obtain ⟨hIs1, he1⟩ := (sa n).binds _ _ _ _ _ _ _ _ _ hb he hIs h1
          cases o with
          | none => cases pure_ok h2; omega
          | some env' =>
            have := ihn.expr _ _ _ _ _ _ _ _ _ hd (he1 env' rfl) hIs1 h2
            omega
        · cases hce
      · cases hce
    | term ty t args =>
      rw [evalExpr.eq_7] at h
      simp only [cExpr] at hce
      split at hce
      · rename_i as c1 has hca
        split at hce
        · rename_i d hd
          cases hce
          obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
          have hW1 := ihn.args _ _ _ _ _ _ _ _ _ hca he hIs h1
          obtain ⟨hIs1, hv1⟩ := (sa n).args _ _ _ _ _ _ _ _ _ has he hIs h1
          cases o with
          | none => cases pure_ok h2; omega
          | some vs =>
            have := ihn.apply _ _ _ _ _ _ _ _ _ _ hd (hv1 vs rfl) hIs1 h2
            omega
        · cases hce
      · cases hce
  · -- evalArgs
    intro es aenv c env s tr r s' tr' hce he hIs h
    cases es with
    | nil => rw [evalArgs.eq_2] at h; cases pure_ok h; omega
    | cons e es =>
      rw [evalArgs.eq_3] at h
      simp only [cArgs] at hce
      split at hce
      · rename_i c1 d h1c h2c
        cases hce
        obtain ⟨a, ha⟩ := cExpr_aExpr e aenv c1 h1c
        obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have hW1 := ihn.expr _ _ _ _ _ _ _ _ _ h1c he hIs h1
        obtain ⟨hIs1, -⟩ := (sa n).expr _ _ _ _ _ _ _ _ _ ha he hIs h1
        cases o with
        | none => cases pure_ok h2; omega
        | some v =>
          obtain ⟨o2, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
          have hW2 := ihn.args _ _ _ _ _ _ _ _ _ h2c he hIs1 h3
          cases o2 with
          | none => cases pure_ok h4; omega
          | some vs => cases pure_ok h4; omega
      · cases hce
  · -- evalBinds
    intro bs aenv c env s tr r s' tr' hce he hIs h
    cases bs with
    | nil => rw [evalBinds.eq_2] at h; cases pure_ok h; omega
    | cons b bs =>
      obtain ⟨x, ty, e⟩ := b
      rw [evalBinds.eq_3] at h
      simp only [cBinds] at hce
      split at hce
      · rename_i a c1 ha hc1
        split at hce
        · rename_i d hd
          cases hce
          obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
          have hW1 := ihn.expr _ _ _ _ _ _ _ _ _ hc1 he hIs h1
          obtain ⟨hIs1, hv1⟩ := (sa n).expr _ _ _ _ _ _ _ _ _ ha he hIs h1
          cases o with
          | none => cases pure_ok h2; omega
          | some v =>
            simp only at h2
            split at h2
            · have := ihn.binds _ _ _ _ _ _ _ _ _ hd (envOK_set he (hv1 v rfl) x) hIs1 h2
              omega
            · exact (throw_ok h2).elim
        · cases hce
      · cases hce
  · -- applyTerm
    intro ty t as c vs s tr r s' tr' hca hvs hIs h
    unfold cApply at hca
    split at hca
    · rename_i hb
      exact (holds2_bot hb hvs).elim
    cases ht : termOf p t with
    | error e =>
      rw [applyTerm.eq_2] at h
      obtain ⟨term', s1, h1, h2⟩ := bind_ok h
      obtain ⟨_, ht', -⟩ := liftM_ok h1
      rw [ht] at ht'; cases ht'
    | ok term =>
      rw [ht] at hca
      simp only at hca
      cases hk : term.kind with
      | enumVariant k =>
        rw [applyTerm.eq_2] at h
        obtain ⟨term', s1, h1, h2⟩ := bind_ok h
        obtain ⟨_, ht', he⟩ := liftM_ok h1
        rw [ht] at ht'; cases ht'; cases he
        rw [hk] at h2
        cases pure_ok h2
        omega
      | struct =>
        rw [applyTerm.eq_2] at h
        obtain ⟨term', s1, h1, h2⟩ := bind_ok h
        obtain ⟨_, ht', he⟩ := liftM_ok h1
        rw [ht] at ht'; cases ht'; cases he
        rw [hk] at h2
        cases pure_ok h2
        omega
      | decl flags ctor ex =>
        rw [hk] at hca
        cases ctor with
        | none =>
          rw [applyTerm.eq_2] at h
          obtain ⟨term', s1, h1, h2⟩ := bind_ok h
          obtain ⟨_, ht', he⟩ := liftM_ok h1
          rw [ht] at ht'; cases ht'; cases he
          rw [hk] at h2
          exact (throw_ok h2).elim
        | some c' =>
          cases c' with
          | internal =>
            simp only at hca
            split at hca
            · rename_i a' hora
              cases hca
              have := hor cfg hc (n + 1) ty t as vs _ s tr r s' tr' hora hvs h
              omega
            · split at hca
              · obtain ⟨ins, hm, hle⟩ := ctabGet_le hca
                exact hroot ty t term flags ex ins c vs s tr r s' tr' ht hk
                  (fun rl hrl => .inl (chkCost_mem hct hm rl hrl)) (holds2_le hle hvs) hIs h
              · cases hca
          | external fn =>
            simp only at hca
            split at hca
            · rename_i hpre
              rw [applyTerm.eq_2] at h
              obtain ⟨term', s1, h1, h2⟩ := bind_ok h
              obtain ⟨_, ht', he⟩ := liftM_ok h1
              rw [ht] at ht'; cases ht'; cases he
              rw [hk] at h2
              simp only at h2
              split at h2
              · exact (throw_ok h2).elim
              · obtain ⟨g, s2, h3, h4⟩ := bind_ok h2
                cases get_ok h3
                simp only at h4
                split at h4
                · rename_i v st' hcv
                  obtain ⟨u, s3, h5, h6⟩ := bind_ok h4
                  cases set_ok h5
                  cases pure_ok h6
                  exact hext as vs term v s _ c hvs hpre hca hcv
                · split at h4
                  · cases pure_ok h4; omega
                  · exact (throw_ok h4).elim
                · exact (throw_ok h4).elim
            · cases hca
  · -- matchRule
    intro rl ins cs vs s tr env s' tr' hcs hins hIs h
    rw [matchRule.eq_2] at h
    obtain ⟨g, s1, h1, h2⟩ := bind_ok h
    cases get_ok h1
    simp only at h2
    obtain ⟨o, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    obtain ⟨_, hma, he⟩ := liftM_ok h3
    cases he
    cases o with
    | none => cases pure_ok h4
    | some env0 =>
      obtain ⟨aenv0, hm0, he0⟩ := patArgs_env sa hins hIs hma
      obtain ⟨c0, hc0, hcif⟩ := mapM_some_mem hcs aenv0 hm0
      have := ihn.iflets _ _ _ _ _ _ _ _ _ hcif he0 hIs h4
      have := le_foldl_max hc0 0
      omega
  · -- matchIfLets
    intro ils aenv c env s tr env' s' tr' hci he hIs h
    cases ils with
    | nil => rw [matchIfLets.eq_2] at h; cases pure_ok h; omega
    | cons il ils =>
      rw [matchIfLets.eq_3] at h
      rw [cIfLets.eq_2] at hci
      split at hci
      · rename_i a c1 ha hc1
        split at hci
        · rename_i ds hds
          cases hci
          obtain ⟨o, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
          have hW1 := ihn.expr _ _ _ _ _ _ _ _ _ hc1 he hIs h1
          obtain ⟨hIs1, hv1⟩ := (sa n).expr _ _ _ _ _ _ _ _ _ ha he hIs h1
          cases o with
          | none => cases pure_ok h2
          | some v =>
            obtain ⟨g, s2, h3, h4⟩ := bind_ok h2
            cases get_ok h3
            simp only at h4
            obtain ⟨o2, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
            obtain ⟨_, hmp, he2⟩ := liftM_ok h5
            cases he2
            cases o2 with
            | none => cases pure_ok h6
            | some env1 =>
              obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
                cases n with
                | zero => rw [evalExpr.eq_1] at h1; exact (throw_ok h1).elim
                | succ k => exact ⟨k, rfl⟩
              obtain ⟨aenv1, hm1, he1⟩ := pat_env sa ha he hIs h1 hmp
              obtain ⟨d, hd, hcd⟩ := mapM_some_mem hds aenv1 hm1
              have := ihn.iflets _ _ _ _ _ _ _ _ _ hcd he1 hIs1 h6
              have := le_foldl_max hd 0
              omega
        · cases hci
      · cases hci

/-- **A root term whose rules cost at most `c` or never match** grows `W` by at most `c`. -/
theorem cost_root (hc : cfg.checkOverlap = false) (sa : ∀ n, SoundAt md cfg tab n)
    (hext : ExtW f ctx apre aw W) (hor : OracleW p f ctx aOracle W)
    (hct : chkCost p tab aw ctab aext actor apre aOracle = true)
    {vs : List V} {c : Nat} {ty : TypeId} {t : TermId} {term : Term} {flags : TermFlags}
    {ex : Option Extractor} {ins : List AW} {s : LState} {tr : Array RuleId} {r : Option V}
    {s' : LState} {tr' : Array RuleId}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hrules : ∀ rl ∈ p.rulesOf t, cRuleLe p tab aw ctab aext actor apre aOracle ins c rl = true ∨
      ∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1))
    (hins : Holds2 f ctx ins vs) (hIs : md.Is s) {n : Nat}
    (h : (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    W s' ≤ W s + c :=
  (costAt hc sa hext hor hct n).root _ _ _ _ _ _ _ _ _ _ _ _ _ ht hk hrules hins hIs h

/-- **A root term whose rules cost at most `c`, never match, or are checked by hand**
(`HandW`: at a fuel leaving every hand-checked match and right-hand side 1000 steps) grows `W`
by at most `c` (`root_hand` for the cost). -/
theorem cost_root_hand (hc : cfg.checkOverlap = false) (sa : ∀ n, SoundAt md cfg tab n)
    (hext : ExtW f ctx apre aw W) (hor : OracleW p f ctx aOracle W)
    (hct : chkCost p tab aw ctab aext actor apre aOracle = true)
    {vs : List V} {c : Nat} {Hand : Rule → Prop}
    (hhand : ∀ rl, Hand rl → HandW p ctx vs rl W c)
    {ty : TypeId} {t : TermId} {term : Term} {flags : TermFlags} {ex : Option Extractor}
    {ins : List AW} {s : LState} {tr : Array RuleId} {r : Option V} {s' : LState}
    {tr' : Array RuleId}
    (ht : termOf p t = .ok term) (hk : term.kind = .decl flags (some .internal) ex)
    (hrules : ∀ rl ∈ p.rulesOf t, cRuleLe p tab aw ctab aext actor apre aOracle ins c rl = true ∨
      (∀ m s0 env s1, (matchRule p (sem ctx) cfg m rl vs).run s0 ≠ .ok (some env, s1)) ∨ Hand rl)
    (hins : Holds2 f ctx ins vs) (hIs : md.Is s) {n : Nat} (hn : 1002 + (p.rulesOf t).length ≤ n)
    (h : (applyTerm p (sem ctx) cfg (n + 1) ty t vs).run (s, tr) = .ok (r, (s', tr'))) :
    W s' ≤ W s + c := by
  have ca := costAt hc sa hext hor hct
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
    · cases pure_ok h2; omega
    · exact (throw_ok h2).elim
  | some re =>
    obtain ⟨rl, env⟩ := re
    obtain ⟨hrl, m, hmn, hmatch⟩ := selectRule_some_lt hc h1
    simp only at h2
    obtain ⟨ev, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
    have hfin : s' = s2 := by
      cases ev with
      | some v =>
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        have hf := fire_ok h5
        cases pure_ok h6
        exact hf
      | none => cases pure_ok h4; rfl
    subst hfin
    rcases hrules rl hrl with hok | hno | hhd
    · obtain ⟨cs, envs, ds, hcs, hae, hds, hle⟩ := cRuleLe_inv hok
      have hW1 := (ca m).mrule _ _ _ _ _ _ _ _ _ hcs hins hIs hmatch
      obtain ⟨hIs1, aenv, haenv, he1⟩ := (sa m).mrule _ _ _ _ _ _ _ _ _ hae hins hIs hmatch
      obtain ⟨d, hd, hcd⟩ := mapM_some_mem hds aenv haenv
      have hd' := le_foldl_max hd 0
      have hW2 := (ca n).expr _ _ _ _ _ _ _ _ _ hcd he1 hIs1 h3
      omega
    · exact absurd hmatch (hno m _ _ _)
    · obtain ⟨-, m', hm', hmatch'⟩ := selectRule_some hc h1
      exact hhand rl hhd cfg hc m' n s tr env _ ev _ tr2 (by omega) (by omega) hmatch' h3

end Cost

end Backend.Proof.Cov
