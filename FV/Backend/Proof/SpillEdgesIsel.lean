import FV.Backend.Proof.IselTermFactsRules

/-!
# The last instruction of a terminator's lowering (V4, the spill allocator's CFG facts)

`IselTermFactsRules` proves that the terminator rules append a non-empty list of instructions
(`TermShape`, `BranchShape`). The CFG facts `EdgesOk` need the last instruction itself: the
code of a `return`/`trap` ends in an instruction without successors (`TermShapeT`), that of a
`jump` in the `jump` (`JumpShape`). Same symbolic executions, stronger conclusions.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The rule appended a non-empty list of instructions whose last has no successors. -/
def TermShapeT (st st' : LState) : Prop :=
  ∃ (ms : List MInst) (i : MInst), st'.emitted = st.emitted ++ (ms ++ [i]).toArray ∧ i.targets = []

/-- The rule appended exactly a `jump` to the only target. -/
def JumpShape (st st' : LState) (targets : List Label) : Prop :=
  ∃ l, st'.emitted = st.emitted ++ (([] : List MInst) ++ [MInst.jump l]).toArray ∧ targets = [l]

/-- `LowerTermShapeOk` with the stronger conclusion. -/
def LowerTermShapeOkT (p : Program) (r : Rule) : Prop :=
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
    TermShapeT st st'

theorem trap_shapeT {p : Program} (hp : Data p) : LowerTermShapeOkT p rule_lower_2237 := by
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
theorem ret_shapeT {p : Program} (hp : Data p) : LowerTermShapeOkT p rule_lower_2574 := by
  intro f ctx hctx ti t data hrt hd hi cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kR := fun n (hn : 60 ≤ n) xs s v s' h => lower_return_ok hp (ctx := ctx) hc (n := n)
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

/-- **`jump`** (`rule_lower_3270`): exactly the `jump`. -/
theorem jump_shapeJ {p : Program} (hp : Data p) {ctx : Ctx}
    {ti : Nat} {d : Clif.BlockCall} {data : V} {targets : List Label}
    (hd : termData (.jump d) = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_3270 [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_3270.rhs env').run s1 = .ok (some out, (st', tr'))) :
    JumpShape st st' targets := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kJ := fun n (hn : 30 ≤ n) t s v s' h => aarch64_jump_ok hp (ctx := ctx) hc (n := n) (t := t)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  rw [termData_jump] at hd; cases hd
  cases hp
  isel_inv [*, rule_lower_3270, ext_single_target_iff, ctor_branch_target_iff] at hmatch heval
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_single_target_iff, ctor_branch_target_iff] at * <;> isel_destruct <;>
    subst_vars)
  have h661 := ‹ApplyInternal _ _ _ _ 46 661 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kJ _ (by omega) _ _ _ _ h661
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_jump] at hmi
  cases hmi
  simp only at hs1 hs2
  subst hs2
  rw [hs1]
  exact ⟨_, by simp [LState.emit], rfl⟩

/-- **`lower` on a `return`/`trap`** appends code ending in an instruction without successors. -/
theorem termShapeT_runTerm {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {st : LState} {out : V} {st' : LState}
    {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ti] st = .ok (some out, st', tr)) : TermShapeT st st' := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_rule h
  cases hroot : termRootRule r
  · exact absurd hmatch (termUnmatchable r hr hroot f ctx hctx ti t data hrt hd hi {} m (st, #[])
      env' s1)
  · simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
    rcases hroot with e | e
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2237 (by rw [e]; rfl)] at hfirst hmatch heval
      exact trap_shapeT data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2574 (by rw [e]; rfl)] at hfirst hmatch heval
      exact ret_shapeT data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval

/-- **`lower_branch` on a `jump`** appends exactly the `jump`. -/
theorem jumpShape_runTerm {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    {d : Clif.BlockCall} {data : V} {targets : List Label}
    (hd : termData (.jump d) = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    JumpShape st st' targets := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_branch_rule h
  have hrt : retOrTrap (.jump d) = false := rfl
  cases hroot : closureRoot r
  · exact absurd hmatch (branchExcludedUnmatchable r hr hroot f ctx hctx ti (.jump d) data targets hrt
      hd hi {} m (st, #[]) env' s1)
  · have hr' := hr
    rw [show TId.lower_branch = 687 from rfl, data_program.r687] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hroot (by decide +kernel)
    · have hf := ruleFmt_term data_program (r := rule_lower_3251) rfl data_program.t2452
        term_2452_kind hd hi hmatch
      simp [termFmt] at hf
    · have hf := ruleFmt_term data_program (r := rule_lower_3257) rfl data_program.t2452
        term_2452_kind hd hi hmatch
      simp [termFmt] at hf
    · exact absurd hroot (by decide +kernel)
    · exact absurd hroot (by decide +kernel)
    · have hf := ruleFmt_term data_program (r := rule_lower_3231) rfl data_program.t2452
        term_2452_kind hd hi hmatch
      simp [termFmt] at hf
    · exact jump_shapeJ data_program hd hi rfl hm hn hmatch heval
    · have hf := ruleFmt_term data_program (r := rule_lower_3277) rfl data_program.t2451
        term_2451_kind hd hi hmatch
      simp [termFmt] at hf

end Backend.Proof
