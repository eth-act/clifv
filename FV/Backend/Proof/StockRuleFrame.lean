import FV.Backend.Proof.IselFlowGen

/-! A constructor frame with complete matched-rule exceptions. Syntax checks are
internal proof obligations; callers still run the original interpreter/program. -/
namespace Isle.Interp.RuleFrame
open Isle.Interp
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def termCtorFree (p : Program) (blocked : Term → Bool) (t : TermId) : Bool :=
  match p.term? t with | none => true | some term => !blocked term

mutual
 def exprTermFree (allowed : TermId → Bool) : Expr → Bool
  | .term _ t args => allowed t && argsTermFree allowed args
  | .let _ binds body => bindsTermFree allowed binds && exprTermFree allowed body
  | _ => true
 def argsTermFree (allowed : TermId → Bool) : List Expr → Bool
  | [] => true
  | e :: es => exprTermFree allowed e && argsTermFree allowed es
 def bindsTermFree (allowed : TermId → Bool) : List (VarId × TypeId × Expr) → Bool
  | [] => true
  | (_,_,e) :: rest => exprTermFree allowed e && bindsTermFree allowed rest
end

def exprCtorFree (p : Program) (blocked : Term → Bool) := exprTermFree (termCtorFree p blocked)
def argsCtorFree (p : Program) (blocked : Term → Bool) := argsTermFree (termCtorFree p blocked)
def bindsCtorFree (p : Program) (blocked : Term → Bool) := bindsTermFree (termCtorFree p blocked)
def ifletsCtorFree (p : Program) (blocked : Term → Bool) (ils : List IfLet) : Bool :=
  ils.all (fun il => exprCtorFree p blocked il.rhs)

private theorem termCtorFree_lookup {p : Program} {blocked : Term → Bool} {t : TermId}
    {term : Term} (free : termCtorFree p blocked t = true) (found : termOf p t = .ok term) :
    blocked term = false := by
  unfold termOf at found
  unfold termCtorFree at free
  cases lookup : p.term? t with
  | none => simp [lookup] at found
  | some actual =>
    simp only [lookup, pure, Except.pure, Except.ok.injEq] at found
    subst actual
    simp only [lookup] at free
    cases value : blocked term <;> simp_all

variable {V σ : Type} (p : Program) (sem : Sem V σ) (cfg : Config)
variable (blocked : Term → Bool) (R : σ → σ → Prop)
structure CtorFreeAt (n : Nat) : Prop where
  expr : ∀ e env s tr r s' tr', exprCtorFree p blocked e = true → (evalExpr p sem cfg n e env).run (s, tr) = .ok (r, (s', tr')) →
    R s s'
  args : ∀ es env s tr r s' tr', argsCtorFree p blocked es = true → (evalArgs p sem cfg n es env).run (s, tr) = .ok (r, (s', tr')) →
    R s s'
  binds : ∀ bs env s tr r s' tr', bindsCtorFree p blocked bs = true → (evalBinds p sem cfg n bs env).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  apply : ∀ ty t vs s tr r s' tr', termCtorFree p blocked t = true → (applyTerm p sem cfg n ty t vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  mrule : ∀ rl vs s tr r s' tr', ifletsCtorFree p blocked rl.iflets = true → (matchRule p sem cfg n rl vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  iflets : ∀ ils env s tr r s' tr', ifletsCtorFree p blocked ils = true → (matchIfLets p sem cfg n ils env).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  tryr : ∀ rl vs s tr r s' tr', ifletsCtorFree p blocked rl.iflets = true → (tryRule p sem cfg n rl vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  also : ∀ rs vs s tr r s' tr', (alsoMatching p sem cfg n rs vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'
  select : ∀ term rs vs s tr r s' tr', (∀ rl ∈ rs, ifletsCtorFree p blocked rl.iflets = true) → (selectRule p sem cfg n term rs vs).run (s, tr) =
    .ok (r, (s', tr')) → R s s'

variable {p sem cfg blocked R}

theorem ctorFreeAt_inductive (hrefl : ∀ s, R s s) (htrans : ∀ a b c, R a b → R b c → R a c)
    (hctor : ∀ term vs s v s', blocked term = false → sem.ctor term vs s = .ok (v, s') → R s s')
    (noOverlap : cfg.checkOverlap = false)
    (special : Rule → Prop)
    (rules : ∀ t rl, rl ∈ p.rulesOf t → ifletsCtorFree p blocked rl.iflets = true ∧
      (exprCtorFree p blocked rl.rhs = true ∨ special rl))
    (exceptional : ∀ n, (∀ k, k < n → CtorFreeAt p sem cfg blocked R k) →
      ∀ rl, special rl → ∀ m vs env s tr mid trm out s' tr',
      (matchRule p sem cfg m rl vs).run (s,tr) = .ok (some env,mid,trm) →
      (evalExpr p sem cfg n rl.rhs env).run (mid,trm) = .ok (out,s',tr') → R s s') :
    ∀ n, CtorFreeAt p sem cfg blocked R n := by
  intro n
  induction n using Nat.strongRecOn with
  | ind fuel earlier =>
   cases fuel with
   | zero =>
     refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> rename_i h <;>
       first
       | (rw [evalExpr.eq_1] at h; exact (throw_ok h).elim)
       | (rw [evalArgs.eq_1] at h; exact (throw_ok h).elim)
       | (rw [evalBinds.eq_1] at h; exact (throw_ok h).elim)
       | (rw [applyTerm.eq_1] at h; exact (throw_ok h).elim)
       | (rw [matchRule.eq_1] at h; exact (throw_ok h).elim)
       | (rw [matchIfLets.eq_1] at h; exact (throw_ok h).elim)
       | (rw [tryRule.eq_1] at h; exact (throw_ok h).elim)
       | (rw [alsoMatching.eq_1] at h; exact (throw_ok h).elim)
       | (rw [selectRule.eq_1] at h; exact (throw_ok h).elim)
   | succ n =>
    have ih := earlier n (Nat.lt_succ_self n)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- evalExpr
      intro e env s tr r s' tr' free h
      cases e with
      | var ty x =>
        rw [evalExpr.eq_2] at h
        split at h
        · cases pure_ok h; exact hrefl s
        · exact (throw_ok h).elim
      | constBool ty b => rw [evalExpr.eq_3] at h; cases pure_ok h; exact hrefl s
      | constInt ty i => rw [evalExpr.eq_4] at h; cases pure_ok h; exact hrefl s
      | constPrim ty nm =>
        rw [evalExpr.eq_5] at h
        split at h
        · cases pure_ok h; exact hrefl s
        · exact (throw_ok h).elim
      | «let» ty bs body =>
        have parts := free
        simp only [exprCtorFree, argsCtorFree, bindsCtorFree, ifletsCtorFree,
          exprTermFree, argsTermFree, bindsTermFree, List.all_cons, Bool.and_eq_true] at parts
        rw [evalExpr.eq_6] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.binds _ _ _ _ _ _ _ parts.1 h1
        cases a with
        | some env' => exact htrans _ _ _ r1 (ih.expr _ _ _ _ _ _ _ parts.2 h2)
        | none => cases pure_ok h2; exact r1
      | term ty t args =>
        have parts := free
        simp only [exprCtorFree, argsCtorFree, bindsCtorFree, ifletsCtorFree,
          exprTermFree, argsTermFree, bindsTermFree, List.all_cons, Bool.and_eq_true] at parts
        rw [evalExpr.eq_7] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.args _ _ _ _ _ _ _ parts.2 h1
        cases a with
        | some vs => exact htrans _ _ _ r1 (ih.apply _ _ _ _ _ _ _ _ parts.1 h2)
        | none => cases pure_ok h2; exact r1
    · -- evalArgs
      intro es env s tr r s' tr' free h
      cases es with
      | nil => rw [evalArgs.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons e es =>
        have parts := free
        simp only [exprCtorFree, argsCtorFree, bindsCtorFree, ifletsCtorFree,
          exprTermFree, argsTermFree, bindsTermFree, List.all_cons, Bool.and_eq_true] at parts
        rw [evalArgs.eq_3] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.expr _ _ _ _ _ _ _ parts.1 h1
        cases a with
        | none => cases pure_ok h2; exact r1
        | some v =>
          obtain ⟨b, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
          have r2 := ih.args _ _ _ _ _ _ _ parts.2 h3
          cases b with
          | some vs => cases pure_ok h4; exact htrans _ _ _ r1 r2
          | none => cases pure_ok h4; exact htrans _ _ _ r1 r2
    · -- evalBinds
      intro bs env s tr r s' tr' free h
      cases bs with
      | nil => rw [evalBinds.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons b bs =>
        obtain ⟨x, ty, e⟩ := b
        have parts := free
        simp only [exprCtorFree, argsCtorFree, bindsCtorFree, ifletsCtorFree,
          exprTermFree, argsTermFree, bindsTermFree, List.all_cons, Bool.and_eq_true] at parts
        rw [evalBinds.eq_3] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.expr _ _ _ _ _ _ _ parts.1 h1
        cases a with
        | none => cases pure_ok h2; exact r1
        | some v =>
          simp only at h2
          split at h2
          · exact htrans _ _ _ r1 (ih.binds _ _ _ _ _ _ _ parts.2 h2)
          · exact (throw_ok h2).elim
    · -- applyTerm
      intro ty t vs s tr r s' tr' free h
      rw [applyTerm.eq_2] at h
      obtain ⟨term, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      obtain ⟨_, found, he⟩ := liftM_ok h1
      cases he
      split at h2
      · cases pure_ok h2; exact hrefl s
      · cases pure_ok h2; exact hrefl s
      · split at h2
        · exact (throw_ok h2).elim
        · obtain ⟨g, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
          cases get_ok h3
          simp only at h4
          split at h4
          · rename_i v st' hc
            obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
            cases set_ok h5
            cases pure_ok h6
            exact hctor _ _ _ _ _ (termCtorFree_lookup free found) hc
          · split at h4
            · cases pure_ok h4; exact hrefl s
            · exact (throw_ok h4).elim
          · exact (throw_ok h4).elim
      · split at h2
        · exact (throw_ok h2).elim
        · obtain ⟨sel, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
          have r1 := ih.select _ _ _ _ _ _ _ _ (fun rl member => (rules t rl member).1) h3
          cases sel with
          | none =>
            simp only at h4
            split at h4
            · cases pure_ok h4; exact r1
            · exact (throw_ok h4).elim
          | some selected =>
            obtain ⟨rl,env⟩ := selected
            simp only at h4
            obtain ⟨ev, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
            obtain ⟨member,m,bound,matched⟩ := selectRule_some noOverlap h3
            have r2 : R s s3 := by
              rcases (rules t rl member).2 with safe | chosen
              · exact htrans _ _ _ r1 (ih.expr _ _ _ _ _ _ _ safe h5)
              · exact exceptional n (fun k hk => earlier k (Nat.lt_succ_of_lt hk))
                  rl chosen m vs env s tr s2 tr2 ev s3 tr3 matched h5
            split at h6
            · obtain ⟨u, ⟨s4, tr4⟩, h7, h8⟩ := bind_ok h6
              have hf := fire_ok h7
              cases pure_ok h8
              simp only at hf
              subst hf
              exact r2
            · cases pure_ok h6; exact r2
      · exact (throw_ok h2).elim
    · -- matchRule
      intro rl vs s tr r s' tr' free h
      rw [matchRule.eq_2] at h
      obtain ⟨g, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
      cases get_ok h1
      simp only at h2
      obtain ⟨m, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
      obtain ⟨_, -, he⟩ := liftM_ok h3
      cases he
      cases m with
      | none => cases pure_ok h4; exact hrefl s
      | some env => exact ih.iflets _ _ _ _ _ _ _ free h4
    · -- matchIfLets
      intro ils env s tr r s' tr' free h
      cases ils with
      | nil => rw [matchIfLets.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons il ils =>
        have parts := free
        simp only [exprCtorFree, argsCtorFree, bindsCtorFree, ifletsCtorFree,
          exprTermFree, argsTermFree, bindsTermFree, List.all_cons, Bool.and_eq_true] at parts
        rw [matchIfLets.eq_3] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.expr _ _ _ _ _ _ _ parts.1 h1
        cases a with
        | none => cases pure_ok h2; exact r1
        | some v =>
          obtain ⟨g, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
          cases get_ok h3
          simp only at h4
          obtain ⟨m, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
          obtain ⟨_, -, he⟩ := liftM_ok h5
          cases he
          cases m with
          | none => cases pure_ok h6; exact r1
          | some env' => exact htrans _ _ _ r1 (ih.iflets _ _ _ _ _ _ _ parts.2 h6)
    · -- tryRule
      intro rl vs s tr r s' tr' free h
      cases n with
      | zero =>
        rw [tryRule.eq_2] at h
        obtain ⟨g, s1, h1, h2⟩ := bind_ok h
        cases get_ok h1
        obtain ⟨m, s2, h3, -⟩ := bind_ok h2
        rw [matchRule.eq_1] at h3
        exact (throw_ok h3).elim
      | succ k =>
        rcases tryRule_run h with ⟨env, -, hm⟩ | ⟨-, hs⟩
        · exact ih.mrule _ _ _ _ _ _ _ free hm
        · cases hs; exact hrefl s
    · -- alsoMatching
      intro rs vs s tr r s' tr' h
      cases rs with
      | nil => rw [alsoMatching.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons rl rs =>
        rw [alsoMatching.eq_3] at h
        obtain ⟨g, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        cases get_ok h1
        obtain ⟨m, ⟨s2, tr2⟩, h3, h4⟩ := bind_ok h2
        obtain ⟨u, ⟨s3, tr3⟩, h5, h6⟩ := bind_ok h4
        cases set_ok h5
        obtain ⟨rest, ⟨s4, tr4⟩, h7, h8⟩ := bind_ok h6
        cases pure_ok h8
        exact ih.also _ _ _ _ _ _ _ h7
    · -- selectRule
      intro term rs vs s tr r s' tr' free h
      cases rs with
      | nil => rw [selectRule.eq_2] at h; cases pure_ok h; exact hrefl s
      | cons rl rs =>
        rw [selectRule.eq_3] at h
        obtain ⟨a, ⟨s1, tr1⟩, h1, h2⟩ := bind_ok h
        have r1 := ih.tryr _ _ _ _ _ _ _ (free rl (List.mem_cons_self ..)) h1
        cases a with
        | none => exact htrans _ _ _ r1 (ih.select _ _ _ _ _ _ _ _ (fun r member => free r (List.mem_cons_of_mem _ member)) h2)
        | some env =>
          simp only [noOverlap, Bool.false_eq_true, ↓reduceIte] at h2
          cases pure_ok h2; exact r1

end Isle.Interp.RuleFrame
