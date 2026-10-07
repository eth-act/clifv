import FV.Backend.Proof.DefGenPat
import FV.Backend.Proof.KillGen

/-!
# Definedness of the ISLE runs: soundness of the abstract interpreter

For a run of the driver's semantics `sem ctx` started at `s0`: the defined vregs at state `s`
are the reached CLIF values' vregs and the fresh defs of the instructions emitted since `s0`
(`Dn`); the state invariant `IsD` says every emitted instruction reads defined vregs (of the
instructions before it). `soundAt` (by induction on the fuel): if the rules of the terms `T`
check (`TabOK`), the extern constructors, extractors, oracles and constructor-tree terms meet
their transfers (`DModel`), then every abstract evaluation describes the run.
-/

namespace Backend.Proof.DefGen

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Spill Backend.Proof.Kill
  Backend.Proof.DefRun Isle Isle.Aarch64 Isle.Interp

/-! ## The state invariant -/

section State
variable (ctx : Ctx) (c : SC) (s0 : LState)

/-- The reached CLIF values' vregs. -/
def D0 : Nat → Prop := fun n => n < ctx.valDef.size ∧ c.R n

/-- **The defined vregs** at state `s`. -/
def Dn (s : LState) : Nat → Prop := DD c (D0 ctx c) (emittedSince s0 s)

/-- **The state invariant**: every instruction emitted since `s0` reads defined vregs. -/
def IsD (s : LState) : Prop :=
  (∃ ms : List MInst, s.emitted = s0.emitted ++ ms.toArray ∧
    ∀ (k : Nat) m, ms[k]? = some m → ∀ u ∈ useVregs m, DD c (D0 ctx c) (ms.take k) u) ∧
  c.lo ≤ s.nextVreg

/-- The run relation. -/
def RsD (s s' : LState) : Prop :=
  s.nextVreg ≤ s'.nextVreg ∧ ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray

end State

theorem RsD.refl (s : LState) : RsD s s := ⟨Nat.le_refl _, [], by simp⟩

theorem RsD.trans {a b d : LState} (h1 : RsD a b) (h2 : RsD b d) : RsD a d := by
  obtain ⟨h1, ms1, e1⟩ := h1
  obtain ⟨h2, ms2, e2⟩ := h2
  exact ⟨Nat.le_trans h1 h2, ms1 ++ ms2, by simp [e2, e1]⟩

theorem emittedSince_of' {s0 s : LState} {ms : List MInst}
    (h : s.emitted = s0.emitted ++ ms.toArray) : emittedSince s0 s = ms := by
  simp [emittedSince, h]

theorem Dn_mono {ctx : Ctx} {c : SC} {s0 s s' : LState} (hI : IsD ctx c s0 s) (hR : RsD s s') :
    ∀ n, Dn ctx c s0 s n → Dn ctx c s0 s' n := by
  obtain ⟨⟨ms, e, -⟩, -⟩ := hI
  obtain ⟨-, ms', e'⟩ := hR
  have h1 := emittedSince_of' e
  have h2 : emittedSince s0 s' = ms ++ ms' := emittedSince_of' (by rw [e', e]; simp)
  intro n hn
  unfold Dn at hn ⊢
  rw [h1] at hn
  rw [h2]
  rcases hn with hn | ⟨h3, m, hm, h4⟩
  · exact .inl hn
  · exact .inr ⟨h3, m, List.mem_append_left _ hm, h4⟩

/-! ## The model and the table -/

/-- Closed abstract values (summaries) do not depend on the environment. -/
theorem γ_tyA_env {c : SC} {z : Bool} {τ : TypeId} {D : Nat → Prop} {env env' : Isle.Interp.Env V}
    {v : V} (h : γ c (tyA z τ) D env v) : γ c (tyA z τ) D env' v := by
  unfold tyA at h ⊢
  split <;> (try split) <;> (try split) <;> simp_all [γ]

theorem γL_tyA_env {c : SC} {z : Bool} {D : Nat → Prop} {env env' : Isle.Interp.Env V} :
    ∀ {τs : List TypeId} {vs : List V}, γL c (τs.map (tyA z)) D env vs →
      γL c (τs.map (tyA z)) D env' vs
  | [], [], _ => trivial
  | _ :: _, _ :: _, h => ⟨γ_tyA_env h.1, γL_tyA_env h.2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- **The facts about the embedding** the soundness proof needs. -/
structure DModel (p : Program) (ctx : Ctx) (c : SC) (s0 : LState) : Prop where
  ext : ExtOK c ctx
  ctor : ∀ (t : TermId) (term : Term) (as : List A) (e e' : AEnv) (a : A)
    (env : Isle.Interp.Env V) (vs : List V) (s s' : LState) (v : V),
    termOf p t = .ok term → actor e t as = some (a, e') → γL c as (Dn ctx c s0 s) env vs →
    EnvOK c (Dn ctx c s0 s) env e → IsD ctx c s0 s → externCtor ctx term vs s = .ok (v, s') →
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e' ∧
      γ c a (Dn ctx c s0 s') env v
  ctor_fail : ∀ (t : TermId) (term : Term) (as : List A) (e e' : AEnv) (a : A) (vs : List V)
    (s : LState), termOf p t = .ok term → actor e t as = some (a, e') →
    externCtor ctx term vs s = .fail → e' = e
  oracle : ∀ t ∈ oracles, ∀ (cfg : Config), cfg.checkOverlap = false →
    ∀ (n : Nat) (ty : TypeId) (as : List A) (e e' : AEnv) (a : A) (env : Isle.Interp.Env V)
      (vs : List V) (s : LState) (tr : Array RuleId) (r : Option V) (s' : LState)
      (tr' : Array RuleId),
    aOracle e as = some (a, e') → γL c as (Dn ctx c s0 s) env vs →
    EnvOK c (Dn ctx c s0 s) env e → IsD ctx c s0 s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e' ∧
      ∀ v, r = some v → γ c a (Dn ctx c s0 s') env v
  wrap : ∀ (t : TermId) (ct : CT), wrapper p t = some ct → ∀ (cfg : Config),
    cfg.checkOverlap = false → ∀ (n : Nat) (ty : TypeId) (vs : List V) (s : LState)
      (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId),
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    s' = s ∧ ∀ v, r = some v → ∀ (as : List A) (D : Nat → Prop) (env : Isle.Interp.Env V),
      γL c as D env vs → γ c (ctA as ct) D env v

/-- **The rules of the terms `T` check**, with their summaries (arguments without, resp. with,
real registers). -/
def TabOK (p : Program) (T : TermId → Prop) : Prop :=
  ∀ t, T t → t ∉ oracles → wrapper p t = none → ∀ term, termOf p t = .ok term →
    ∀ rl ∈ p.rulesOf t, (∀ u ∈ ruleTerms rl, T u) ∧
      aRule p (term.args.map (tyA false)) (tyA false term.ret) rl = true ∧
      aRule p (term.args.map (tyA true)) (tyA (zp.contains t) term.ret) rl = true

/-! ## Soundness -/

section Sound
variable {p : Program} {ctx : Ctx} {c : SC} {s0 : LState} (M : DModel p ctx c s0)
  {T : TermId → Prop} (htab : TabOK p T) (cfg : Config)

theorem aRule_inv {ins : List A} {out : A} {rl : Rule} (h : aRule p ins out rl = true) :
    ∃ e0 e1 a e2, aPatArgs p ins rl.args (List.replicate rl.vars.length none) = some e0 ∧
      aIfLets p rl.iflets e0 = some e1 ∧ aExpr p rl.rhs e1 = some (a, e2) ∧
      fitsA e2 F a out = true := by
  unfold aRule at h
  split at h
  · rename_i e0 h0
    split at h
    · rename_i e1 h1
      split at h
      · rename_i a e2 h2
        exact ⟨e0, e1, a, e2, h0, h1, h2, h⟩
      · cases h
    · cases h
  · cases h

/-- The soundness statements at fuel `n`. -/
structure SoundAt (n : Nat) : Prop where
  expr : ∀ (x : Isle.Expr) (e e' : AEnv) (a : A) (env : Isle.Interp.Env V) (s : LState)
    (tr : Array RuleId) (r : Option V) (s' : LState) (tr' : Array RuleId),
    (∀ u ∈ exprTerms x, T u) → aExpr p x e = some (a, e') →
    EnvOK c (Dn ctx c s0 s) env e → IsD ctx c s0 s →
    (evalExpr p (sem ctx) cfg n x env).run (s, tr) = .ok (r, (s', tr')) →
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e' ∧
      ∀ v, r = some v → γ c a (Dn ctx c s0 s') env v
  args : ∀ (xs : List Isle.Expr) (e e' : AEnv) (as : List A) (env : Isle.Interp.Env V)
    (s : LState) (tr : Array RuleId) (r : Option (List V)) (s' : LState) (tr' : Array RuleId),
    (∀ u ∈ exprTermsL xs, T u) → aArgs p xs e = some (as, e') →
    EnvOK c (Dn ctx c s0 s) env e → IsD ctx c s0 s →
    (evalArgs p (sem ctx) cfg n xs env).run (s, tr) = .ok (r, (s', tr')) →
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e' ∧
      ∀ vs, r = some vs → γL c as (Dn ctx c s0 s') env vs
  binds : ∀ (bs : List (VarId × TypeId × Isle.Expr)) (e e' : AEnv) (env : Isle.Interp.Env V)
    (s : LState) (tr : Array RuleId) (r : Option (Isle.Interp.Env V)) (s' : LState)
    (tr' : Array RuleId),
    (∀ u ∈ bindTerms bs, T u) → aBinds p bs e = some e' →
    EnvOK c (Dn ctx c s0 s) env e → IsD ctx c s0 s →
    (evalBinds p (sem ctx) cfg n bs env).run (s, tr) = .ok (r, (s', tr')) →
    IsD ctx c s0 s' ∧ RsD s s' ∧ ∀ env', r = some env' → EnvOK c (Dn ctx c s0 s') env' e'
  apply : ∀ (ty : TypeId) (t : TermId) (as : List A) (e e' : AEnv) (a : A)
    (env : Isle.Interp.Env V) (vs : List V) (s : LState) (tr : Array RuleId) (r : Option V)
    (s' : LState) (tr' : Array RuleId),
    T t → aApply p ty t as e = some (a, e') → γL c as (Dn ctx c s0 s) env vs →
    EnvOK c (Dn ctx c s0 s) env e → IsD ctx c s0 s →
    (applyTerm p (sem ctx) cfg n ty t vs).run (s, tr) = .ok (r, (s', tr')) →
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env e' ∧
      ∀ v, r = some v → γ c a (Dn ctx c s0 s') env v
  iflets : ∀ (ils : List IfLet) (e e' : AEnv) (env : Isle.Interp.Env V) (s : LState)
    (tr : Array RuleId) (env' : Isle.Interp.Env V) (s' : LState) (tr' : Array RuleId),
    (∀ il ∈ ils, (∀ u ∈ patTerms il.lhs, T u) ∧ ∀ u ∈ exprTerms il.rhs, T u) →
    aIfLets p ils e = some e' → EnvOK c (Dn ctx c s0 s) env e → IsD ctx c s0 s →
    (matchIfLets p (sem ctx) cfg n ils env).run (s, tr) = .ok (some env', (s', tr')) →
    IsD ctx c s0 s' ∧ RsD s s' ∧ EnvOK c (Dn ctx c s0 s') env' e'


theorem Cl_noAtoms {b z : Bool} {D : Nat → Prop} {v : V} (hr : regsU v = []) (hv : v.valsIn = [])
    (hi : v.instsIn = []) : Cl c b z D v :=
  ⟨by simp [hr], by simp [hv], by simp [hi]⟩

theorem γ_int (ty : TypeId) (i : Int) {D : Nat → Prop} {env : Isle.Interp.Env V} :
    γ c (.cl false false) D env ((sem ctx).int ty i) :=
  Cl_noAtoms (by simp [sem, regsU]) (by simp [sem, V.valsIn]) (by simp [sem, V.instsIn])

theorem γ_bool (b : Bool) {D : Nat → Prop} {env : Isle.Interp.Env V} :
    γ c (.cl false false) D env ((sem ctx).bool b) :=
  Cl_noAtoms (by simp [sem, regsU]) (by simp [sem, V.valsIn]) (by simp [sem, V.instsIn])

theorem γ_prim {ty : TypeId} {nm : String} {v : V} (h : (sem ctx).prim ty nm = some v)
    {D : Nat → Prop} {env : Isle.Interp.Env V} : γ c (.cl false false) D env v := by
  simp only [sem] at h
  split at h
  · obtain ⟨t, -, rfl⟩ := Option.map_eq_some_iff.mp h
    exact Cl_noAtoms (by simp [regsU]) (by simp [V.valsIn]) (by simp [V.instsIn])
  · cases h

theorem getElem_env {D : Nat → Prop} {env : Isle.Interp.Env V} {e : AEnv} (he : EnvOK c D env e)
    {x : Nat} {a : A} (hx : e[x]? = some (some a)) : ∃ w, env[x]? = some (some w) :=
  let ⟨w, hw, _⟩ := (he.2 x).2 a hx
  ⟨w, hw⟩

end Sound

end Backend.Proof.DefGen
