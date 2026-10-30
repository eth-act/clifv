import FV.Backend.Proof.IselCtl
import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.IselTermFactsBase

/-!
# The last instruction of a `return`/`trap` lowering is a terminator

`prepare` (`VCode.cfg`) requires every block to end in a terminator (`MInst.isTerminator`).
`SpillEdgesIsel` shows the code of a `return`/`trap` ends in an instruction without successors
(`TermShapeT`); that does not say the instruction ends a block. The same symbolic executions of
the two root rules (`rule_lower_2237`: `udf`, `rule_lower_2574`: `rets`) with the stronger
conclusion `TermShapeR`: the last instruction is a terminator.
-/

namespace Backend.Proof.Prep

open Backend Backend.Proof Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The rule appended a non-empty list of instructions whose last ends a block. -/
def TermShapeR (st st' : LState) : Prop :=
  ∃ (ms : List MInst) (i : MInst), st'.emitted = st.emitted ++ (ms ++ [i]).toArray ∧
    i.isTerminator = true

/-- `LowerTermShapeOkT` with the conclusion `TermShapeR`. -/
def LowerTermShapeOkR (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V), retOrTrap t = true → termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti]).run (st, tr) = .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    TermShapeR st st'

set_option maxHeartbeats 800000 in
/-- **`trap`** (`rule_lower_2237`) ends in `udf`. -/
theorem trap_shapeR {p : Program} (hp : Data p) : LowerTermShapeOkR p rule_lower_2237 := by
  intro f ctx hctx ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kU := fun n (hn : 30 ≤ n) s c v s' h => udf_ok hp (ctx := ctx) hc (n := n) (s := s) (c := c)
    (v := v) (s' := s') hn h
  have kS := fun n (hn : 60 ≤ n) i s v s' h => side_effect_inst_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  cases t with
  | ret xs =>
    rw [termData_ret] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_2237] at hmatch
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    simp at *
  | trap c =>
    rw [termData_trap] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_2237] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [] at * <;> isel_destruct <;> subst_vars)
    have h528 := ‹ApplyInternal _ _ _ _ 46 528 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kU _ (by omega) _ _ _ _ h528
    have h243 := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
    obtain ⟨mi, hmi, hs2, rfl⟩ := kS _ (by omega) _ _ _ _ h243
    simp only at hs1 hs2
    subst hs2
    rw [hs1]
    rw [ofV_udf] at hmi
    cases hmi
    exact ⟨[], .udf c, by simp [LState.emit], rfl⟩
  | _ => simp [retOrTrap] at hrt

set_option maxHeartbeats 800000 in
/-- **`return`** (`rule_lower_2574`) ends in `rets`. -/
theorem ret_shapeR {p : Program} (hp : Data p) : LowerTermShapeOkR p rule_lower_2574 := by
  intro f ctx hctx ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kR := fun n (hn : 60 ≤ n) xs s v s' h => lower_return_ok hp (ctx := ctx) hc hctx.homeCls_int (n := n)
    (xs := xs) (s := s) (v := v) (s' := s') hn h
  cases t with
  | trap c =>
    rw [termData_trap] at hd; cases hd
    cases hp
    isel_inv [*, rule_lower_2574] at hmatch
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    simp at *
  | ret xs =>
    rw [termData_ret] at hd; cases hd
    cases hp
    ctl_inv [*, rule_lower_2574] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [ext_value_list_slice_iff] at * <;> isel_destruct <;> subst_vars)
    have h294 := ‹ApplyInternal _ _ _ _ 25 294 _ _ _ _›
    obtain ⟨rs, hrs, ps, hps, hs, -⟩ := kR _ (by omega) _ _ _ _ h294
    simp only at hs
    subst hs
    exact ⟨[], .rets (rs.zip ps), by simp [LState.emit], rfl⟩
  | _ => simp [retOrTrap] at hrt

/-- **`lower` on a `return`/`trap`** appends code ending in a terminator. -/
theorem termShapeR_runTerm {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {st : LState} {out : V} {st' : LState}
    {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ti] st = .ok (some out, st', tr)) : TermShapeR st st' := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_rule h
  cases hroot : termRootRule r
  · exact absurd hmatch (termUnmatchable r hr hroot f ctx hctx ti t data hrt hd hi {} m (st, #[])
      env' s1)
  · simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
    rcases hroot with e | e
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2237 (by rw [e]; rfl)] at hfirst hmatch heval
      exact trap_shapeR data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2574 (by rw [e]; rfl)] at hfirst hmatch heval
      exact ret_shapeR data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval

end Backend.Proof.Prep
