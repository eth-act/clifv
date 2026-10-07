import FV.Opt.Proof.RuleSkelEmbed

/-!
# Rule-proof infrastructure: `iabs` and `truthy` if-lets

**`iabs`** (`rule_auto_a`). `Sem.iabs x = if x.msb then -x else x` is not unfolded by
`sem_simp`, so `bv_decide` saw it as an atom. `iabs_bif` is its `bif` normal form; `sem_simp_a` is
`sem_simp_b` followed by it. `rule_bits_a` cancels products of negations (`arithmetic.isle` 38,
`imul (ineg x) (ineg y)`) by `BitVec.neg_mul_neg` before any type split (a 128-bit product is out
of reach of `bv_decide`), and drops `rule_bits_b`'s `rfl`/`ac_rfl` attempts: with them, the
`iabs` goals stopped at the maximum recursion depth, an error `first` does not catch.

**`truthy` in a `simplify` if-let** (`rule_auto_t`, `rule_auto_tt`). `(if-let x (truthy v))` calls
the multi term `truthy` (`bitops.isle` 110-122). `truthy_iflets` lifts `truthy_sound`
(`RuleSkelEmbed.lean`) to an if-let at any variable indices followed by any further if-lets: each
environment comes from one run of the remaining if-lets on the environment binding `x` to a class
with `v`'s truthiness, from a later state. `rule_truthy_iflet` applies it inside the `RuleOk`
template, moving the left-hand side's value facts to that state (`opt_den_move`);
`truthy_value_type` evaluates a following `value_type`/`ty_int_ref_scalar_64_extract` if-let
on the new class (`bitops.isle` 129); `truthy_close` closes `bmask`/`select` goals by the
truthiness equation.
-/

set_option linter.unusedSimpArgs false

namespace Opt.Proof

open Isle Isle.Opt Clif

/-- `iabs` as `bif` on the sign bit (read by `bv_decide`). -/
theorem iabs_bif {w : Nat} (x : BitVec w) : Sem.iabs x = bif x.msb then -x else x := by
  unfold Sem.iabs; cases x.msb <;> rfl

/-- `sem_simp_b` plus `iabs_bif`. -/
macro "sem_simp_a" : tactic => `(tactic| (
  sem_simp_b
  (try simp only [iabs_bif] at *)))

/-- `rule_bits_b` with `sem_simp_a`, and products of negations cancelled before the type
split. -/
macro "rule_bits_a" : tactic => `(tactic| (
  try simp (disch := assumption) only [asU64_imm64OfBits, Int.natCast_eq_zero, Int.natCast_inj,
    toNat_eq_iff_ofNat, ofInt_imm64OfBits, bne_iff_ne, ne_eq, toNat_eq_zero_iff] at *
  opt_destruct
  all_goals subst_vars
  all_goals first
    | (simp only [val_some_eq, val_mk_same]; done)
    | (first | apply some_val_congr | apply val_congr | skip
       first
         | (simp only [Clif.Sem.binary, Clif.Sem.unary, Clif.Sem.iadd, Clif.Sem.imul, Clif.Sem.band,
              Clif.Sem.bor, Clif.Sem.bxor]
            ac_rfl)
         | (simp only [Clif.Sem.binary, Clif.Sem.unary, Clif.Sem.imul, Clif.Sem.ineg,
              BitVec.neg_mul_neg]; done)
         | (opt_cases_val <;> opt_cases_ty <;> opt_widths <;> sem_simp_a <;> bv_decide (config := { timeout := 120 })))))

set_option hygiene false in
/-- `rule_finish_b` with `rule_bits_a`. -/
macro "rule_finish_a" : tactic => `(tactic| first
  | (try dsimp only
     apply Valuation.le_trans hle1 hle3
     opt_rw_lhs
     rule_bits_a)
  | (try dsimp only
     apply GraphOk.make_val hG (by opt_P)
     opt_node
     all_goals rule_bits_a))

/-- `rule_auto_b` with `rule_finish_a`. -/
syntax "rule_auto_a " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_a $r:ident) => `(tactic| rule_auto_a $r [])
  | `(tactic| rule_auto_a $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_no_iflets
      rule_lhs hG
      all_goals (rule_rhs [$ts,*]; opt_some_subst; rule_finish_a)))

end Opt.Proof

namespace Opt.Proof

open Isle Isle.Opt Isle.Interp Clif

section
variable {σ : Type} {G : EGraph σ} {P : σ → Prop} {den : σ → Valuation} {fr : Frame} {mem : Mem}

/-- **`truthy` in a `simplify` if-let**: `(if-let x (truthy v))` (`x` variable `j`, `v` variable
`i` bound to the class `c` with value `vc`) followed by the if-lets `rest`. Every resulting
environment comes from one run of `rest` on `env` with `x` bound to a class `m` whose value has
`vc`'s truthiness, started in a state `sa` after `s` and ending in a state `sb` before `s'`. -/
theorem truthy_iflets {p : Isle.Program} (hd : Data p) (hG : GraphOk G P den fr mem)
    {env : Interp.Env V} {i j : Nat} {rest : List IfLet} {c : Nat} {vc : Val}
    (he : env[i]? = some (some (.value c))) (hsz : j < env.size) {n : Nat} (hn : 999 ≤ n)
    {s : St σ} {tr : Array RuleId} {envs : List (Interp.Env V)} {s' : St σ} {tr' : Array RuleId}
    (hP : P s.inner) (hv : den s.inner c = some vc)
    (h : (matchIfLetsN p (sem G) cfg (n + 1)
      (⟨.bind 15 j (.wildcard 15), .term 15 235 [.var 15 i]⟩ :: rest) env).run (s, tr) =
      .ok (envs, (s', tr'))) :
    ∀ e ∈ envs, ∃ m vm sa tra o sb trb, P sa.inner ∧ Valuation.Le (den s.inner) (den sa.inner) ∧
      den sa.inner m = some vm ∧ Sem.truthy vm.bits = Sem.truthy vc.bits ∧
      (matchIfLetsN p (sem G) cfg n rest (env.set! j (some (.value m)))).run (sa, tra) =
        .ok (o, (sb, trb)) ∧
      e ∈ o ∧ Valuation.Le (den sa.inner) (den sb.inner) ∧
      Valuation.Le (den sb.inner) (den s'.inner) := by
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 999 := ⟨n - 999, by omega⟩
  opt_eval h [he]
  have hb : ∀ v, (do
      let x ← (get : M (St σ) (St σ × Array RuleId))
      let envs ← liftM (matchPatN p (sem G) x.fst (Pattern.bind 15 j (Pattern.wildcard 15)) v env)
      bindAll (fun e => matchIfLetsN p (sem G) cfg (n + 999) rest e) envs) =
      matchIfLetsN p (sem G) cfg (n + 999) rest (env.set! j (some v)) := by
    intro v
    funext st
    simp [matchPatN, hsz, bindAll, liftM, bind, StateT.bind, get, getThe,
      MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, monadLift, MonadLift.monadLift,
      StateT.lift, Except.bind]
    split <;> rename_i heq <;> rw [heq]
  simp only [hb] at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i a ha
    obtain ⟨vals, s1, tr1⟩ := a
    obtain ⟨h1, h2, h3⟩ := truthy_sound hd hG c vc _ (by simp [truthyFuel]) s tr vals s1 tr1 hP hv ha
    have hmulti := pres_multi (p := p) (cfg := cfg) (preOrd_SR den) (ctorPres_sem hG) ctorMultiPres_sem
    obtain ⟨-, -, -, -, -, hI'⟩ := hmulti (n + 999)
    intro e he'
    obtain ⟨a, ha', sa, tra, o, sb, trb, hPa, hlea, hrun, ho, hleb⟩ :=
      bindAll_run_mem (preOrd_SR den) (fun v => hI' rest (env.set! j (some v))) _ s1 tr1 envs s' tr' h1 h e he'
    simp only [List.mem_map] at ha'
    obtain ⟨⟨rid, w⟩, hw, rfl⟩ := ha'
    obtain ⟨m, vm, rfl, hm, ht⟩ := h3 rid w hw
    obtain ⟨-, hlab⟩ := hI' rest _ sa tra o sb trb hPa hrun
    exact ⟨m, vm, sa, tra, o, sb, trb, hPa, Valuation.le_trans h2 hlea, hlea _ _ hm, ht, hrun, ho,
      hlab, hleb⟩
end

open Lean Meta Elab Tactic in
/-- `opt_den_move h` (`h : Valuation.Le ρ ρ'`): every hypothesis `ρ x = some a` becomes
`ρ' x = some a`. -/
elab "opt_den_move " h:term : tactic => withMainContext do
  let he ← Term.elabTerm h none
  let ht ← instantiateMVars (← inferType he)
  let rho := ht.getArg! 0
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if let some (_, l, _) := t.eq? then
      if l.isApp && l.appFn! == rho then
        hs := hs.push d.fvarId
  for fv in hs do
    let hn ← mkFreshUserName `hd
    let g ← (← getMainGoal).rename fv hn
    replaceMainGoal [g]
    let hi := mkIdent hn
    evalTactic (← `(tactic| replace $hi:ident := $h _ _ $hi:ident))

set_option hygiene false in
/-- The if-let `(if-let x (truthy v))` (first if-let of the rule): the remaining if-lets run on
the environment binding `x` to a class `m'` with `v`'s truthiness (`ht'`), from a later state
`sa`; the left-hand side's value facts are moved to `sa`, and `hil`/`henv2`/`hle1`/`hle3` are
re-established for the remaining if-lets. -/
macro "rule_truthy_iflet" : tactic => `(tactic| (
  have hT := truthy_iflets hd hG (by simp <;> rfl) (by simp) (by omega) hP1
    (hle1 _ _ ‹den s0.inner _ = some _›) hil
  obtain ⟨m', vm', sa, tra, o', sb, trb, hPa, hlea, hm', ht', hil', ho', hlab, hleb⟩ := hT env2 henv2
  opt_den_move (Valuation.le_trans hle1 hlea)
  clear hT hil henv2 hle1
  have hil := hil'
  have henv2 := ho'
  have hle1 := hlab
  replace hle3 := Valuation.le_trans hleb hle3
  clear hil' ho' hlab hleb))

/-- `Sem.truthy` as read by `bv_decide` (`!=` is not). -/
theorem truthy_not_beq {w : Nat} (x : BitVec w) : Sem.truthy x = !(x == 0#w) := rfl

set_option hygiene false in
/-- The goal after a condition was replaced by one with the same truthiness: `bmask`/`select`
read only the truthiness (`ht'`). -/
macro "truthy_close" : tactic => `(tactic| (
  first | apply some_val_congr | apply val_congr | skip
  simp only [Clif.Sem.bmask, Clif.Sem.select, ht']
  done))

set_option hygiene false in
/-- `rule_finish_w` that first closes the goal by `truthy_close`. -/
macro "rule_finish_t" : tactic => `(tactic| first
  | (try dsimp only
     apply GraphOk.make_val hG (by opt_P)
     opt_node_x
     all_goals (try (show _ < _; first | assumption | omega))
     all_goals (first | truthy_close | ((try simp only [truthy_not_beq] at ht'); rule_bits_w)))
  | rule_finish_w)

/-- `rule_auto_w` for a rule whose first if-let is `(if-let x (truthy v))`. -/
syntax "rule_auto_t " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_t $r:ident) => `(tactic| rule_auto_t $r [])
  | `(tactic| rule_auto_t $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals rule_truthy_iflet
      all_goals rule_iflets
      all_goals (rule_rhs_w [$ts,*]; all_goals (opt_some_subst; (try opt_val_ty_subst); rule_finish_t))))

/-! ### A `value_type` if-let after `truthy` -/

theorem except_error_bind_eq {ε α β : Type} (e : ε) (k : α → Except ε β) :
    (Except.error e >>= k) = .error e := rfl
theorem except_ok_bind_eq {ε α β : Type} (a : α) (k : α → Except ε β) :
    (Except.ok a >>= k) = k a := rfl

theorem bindAll_nil_eq {m : Type → Type} [Monad m] {α β : Type} (f : α → m (List β)) :
    Interp.bindAll f [] = pure [] := rfl

theorem bindAll_cons_eq {m : Type → Type} [Monad m] {α β : Type} (f : α → m (List β)) (a : α)
    (as : List α) :
    Interp.bindAll f (a :: as) = (do let bs ← f a; let cs ← Interp.bindAll f as; pure (bs ++ cs)) := rfl

theorem matchArgsN_nil_eq {V σ : Type} (p : Isle.Program) (msem : MultiSem V σ) (st : σ)
    (env : Interp.Env V) : Interp.matchArgsN p msem st [] [] env = pure [env] := by
  simp [Interp.matchArgsN]

theorem tyIntRefScalar64_i128 : Rust.tyIntRefScalar64 (CTy.ofClif .i128) = none := by decide

set_option hygiene false in
/-- A `value_type` if-let on the class `m'` bound by `rule_truthy_iflet`: split its type read;
an unknown type throws; a known one is `vm'`'s type (`GraphOk.typeOf_eq`), split per type. -/
macro "truthy_value_type" : tactic => `(tactic| (
  opt_eval hil
  rcases hTy : G.typeOf sa.inner m' with _ | xt <;>
    simp only [hTy, except_error_bind_eq, except_ok_bind_eq, toExt_error, toExt_ok_some] at hil
  all_goals (try (simp only [except_throw_bind', except_throw_eq_ok] at hil; done))
  all_goals (
    obtain ⟨tc, bc⟩ := vm'
    have hty := GraphOk.typeOf_eq hG hPa hTy hm'
    try simp only at hty
    subst hty
    rcases Classical.em (xt = .i128) with hxt | hxt
    all_goals first
      | (subst hxt
         opt_eval hil [tyIntRefScalar64_i128, bindAll_nil_eq]
         simp only [Except.ok.injEq, Prod.mk.injEq] at hil
         obtain ⟨rfl, rfl, rfl⟩ := hil
         simp only [List.not_mem_nil] at henv2
         done)
      | (opt_eval hil [tyIntRefScalar64_ofClif hxt, bindAll_cons_eq, bindAll_nil_eq,
           matchArgsN_nil_eq, List.append_nil]
         simp only [Except.ok.injEq, Prod.mk.injEq] at hil
         obtain ⟨rfl, rfl, rfl⟩ := hil
         simp only [List.mem_singleton] at henv2
         subst henv2))))

/-- `rule_auto_t` for `(if-let x (truthy v))` followed by `(if-let (value_type
(ty_int_ref_scalar_64_extract ty)) x)` (`bitops.isle` 129). -/
syntax "rule_auto_tt " ident ("[" (Lean.Parser.Tactic.simpStar <|> Lean.Parser.Tactic.simpErase <|> Lean.Parser.Tactic.simpLemma),* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| rule_auto_tt $r:ident) => `(tactic| rule_auto_tt $r [])
  | `(tactic| rule_auto_tt $r:ident [$ts,*]) => `(tactic| (
      rule_intro $r
      rule_lhs hG
      all_goals rule_truthy_iflet
      all_goals truthy_value_type
      all_goals (rule_rhs_w [$ts,*]; all_goals (opt_some_subst; (try opt_val_ty_subst); rule_finish_t))))

end Opt.Proof
