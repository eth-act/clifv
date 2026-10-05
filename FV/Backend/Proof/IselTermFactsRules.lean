import FV.Backend.Proof.IselTermFactsBase

/-!
# Completeness of `lowerCheck`: the emitted code of the terminator rules

The rule proofs of family Ctl (`IselCtlTerm`, `IselCtlBranch`, `IselCtlBrif`, `IselCtlTbz`,
`IselCtlBrTable`) symbolically execute the root rules of `lower` on `return`/`trap` and of
`lower_branch` on `jump`/`brif`/`br_table` and conclude M4's semantic `LowerTermOk`. This file
re-runs the same symbolic executions for the shape of the emitted code only: every rule appends
a non-empty list of instructions, and for a branch the last one targets the branch's labels
(`TermShape`, `BranchShape`). From there to the driver's calls (`runTerm`): `termShape_runTerm`,
`branchShape_runTerm`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Shapes -/

/-- The rule appended a non-empty list of instructions. -/
def TermShape (st st' : LState) : Prop :=
  ∃ (ms : List MInst) (i : MInst), st'.emitted = st.emitted ++ (ms ++ [i]).toArray

/-- The rule appended a non-empty list of instructions whose last targets `targets`. -/
def BranchShape (st st' : LState) (targets : List Label) : Prop :=
  ∃ (ms : List MInst) (i : MInst), st'.emitted = st.emitted ++ (ms ++ [i]).toArray ∧
    i.targets = targets

/-- One emitted instruction, as a non-empty appended list. -/
theorem emitted_emit (st : LState) (i : MInst) :
    (st.emit i).emitted = st.emitted ++ ([] ++ [i]).toArray := by
  simp [LState.emit]

/-- A fragment followed by one emitted instruction, as a non-empty appended list. -/
theorem emitted_emit_of_frag {st st2 : LState} {ms : List MInst} (hf : Frag st st2 ms)
    (i : MInst) : (st2.emit i).emitted = st.emitted ++ (ms ++ [i]).toArray := by
  simp [LState.emit, hf.emitted]

/-- `LowerTermRuleOk` with the shape conclusion. -/
def LowerTermShapeOk (p : Program) (r : Rule) : Prop :=
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
    TermShape st st'

/-- `BranchRuleOk` with the shape conclusion. -/
def BranchShapeOk (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ti : Nat) (t : Clif.Terminator) (data : V) (targets : List Label), termData t = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ → BrIdxTyped ctx t → TargetsLen t targets →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → ValsBelow ctx st →
    (∀ pre post, p.rulesOf TId.lower_branch = pre ++ r :: post → ∀ r' ∈ pre, ∃ m', 1000 ≤ m' ∧
      ∃ s', (matchRule p (sem ctx) cfg m' r' [.inst ti, .labels targets]).run (st, tr) =
        .ok (none, s')) →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    BranchShape st st' targets

/-! ## `return`, `trap` -/

/-- **`trap`** (`rule_lower_2237`): `udf`. -/
theorem trap_shape {p : Program} (hp : Data p) : LowerTermShapeOk p rule_lower_2237 := by
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
    exact ⟨[], mi, by simp [LState.emit]⟩
  | _ => simp [retOrTrap] at hrt

set_option maxHeartbeats 800000 in
/-- **`return`** (`rule_lower_2574`): `rets`. -/
theorem ret_shape {p : Program} (hp : Data p) : LowerTermShapeOk p rule_lower_2574 := by
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
    exact ⟨[], .rets (rs.zip ps), by simp [LState.emit]⟩
  | _ => simp [retOrTrap] at hrt

/-! ## `jump` -/

/-- **`jump`** (`rule_lower_3270`). -/
theorem jump_shape {p : Program} (hp : Data p) : BranchShapeOk p rule_lower_3270 := by
  intro f ctx hctx ti t data targets hd hi _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kJ := fun n (hn : 30 ≤ n) t s v s' h => aarch64_jump_ok hp (ctx := ctx) hc (n := n) (t := t)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3270) rfl hp.t2462 term_2462_kind hd hi hmatch
  cases t with
  | jump d =>
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
    exact ⟨[], .jump _, by simp [LState.emit], rfl⟩
  | _ => simp [termFmt] at hf

/-! ## `brif` -/

set_option maxHeartbeats 4000000 in
/-- **`lower_brif`** (`rule_lower_3231`): the condition's code, then a conditional branch. -/
theorem brif_shape {p : Program} (hp : Data p) : BranchShapeOk p rule_lower_3231 := by
  intro f ctx hctx ti t data targets hd hi _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE2 := fun n (hn : 30 ≤ n) i j s v s' h => emit_side_effect_inst2_ok hp (ctx := ctx) hc
    (n := n) (i := i) (j := j) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 100 ≤ n) c P (hsh : CondShape c P) a b s v s' h =>
    br_cond_result_ok hp (ctx := ctx) hc (n := n) (c := c) (P := P) (a := a) (b := b) (s := s)
      (v := v) (s' := s') hn hsh h
  have kNZ := fun n (hn : 300 ≤ n) x s c s' hvb h => is_nonzero_cmp_ok hp hc refines_ispec hctx
    (n := n) hn (x := x) (s := s) (c := c) (s' := s') hvb h
  have hf := ruleFmt_term hp (r := rule_lower_3231) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3231] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    have h650 := ‹ApplyInternal _ _ _ _ 123 650 _ _ _ _›
    obtain ⟨ms0, hfr, hsh, -⟩ := kNZ _ (by omega) _ _ _ _ hvb h650
    have h722 := ‹ApplyInternal _ _ _ _ 46 722 _ _ _ _›
    obtain ⟨hs2, rfl⟩ := kB _ (by omega) _ _ hsh _ _ _ _ _ h722
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    rcases hsh with ⟨k, i, sz, rfl, hsz, -⟩ | ⟨k, i, sz, rfl, hsz, -⟩ |
      ⟨mi, mm, cond, rfl, hmi, -, -, hdm, -⟩
    · obtain ⟨mi', hmi', hs3, -⟩ := kE _ (by omega) _ _ _ _ h242
      rw [ofV_condBr_zero hsz] at hmi'
      cases hmi'
      simp only at hs2 hs3
      rw [hs3, hs2]
      exact ⟨ms0, _, emitted_emit_of_frag hfr _, rfl⟩
    · obtain ⟨mi', hmi', hs3, -⟩ := kE _ (by omega) _ _ _ _ h242
      rw [ofV_condBr_notZero hsz] at hmi'
      cases hmi'
      simp only at hs2 hs3
      rw [hs3, hs2]
      exact ⟨ms0, _, emitted_emit_of_frag hfr _, rfl⟩
    · obtain ⟨m1, m2, hs3, hm1, hm2⟩ := kE2 _ (by omega) _ _ _ _ _ h242
      rw [hmi] at hm1
      cases hm1
      rw [ofV_condBr_cond] at hm2
      cases hm2
      simp only at hs2 hs3
      rw [hs3, hs2]
      exact ⟨ms0 ++ [mm], _, emitted_emit_of_frag (hfr.append (Frag.emit_nodef _ hdm)) _, rfl⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 4000000 in
/-- **`tbnz`** (`rule_lower_3251`). -/
theorem tbnz_shape {p : Program} (hp : Data p) : BranchShapeOk p rule_lower_3251 := by
  intro f ctx hctx ti t data targets hd hi _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kT := fun n (hn : 60 ≤ n) a b r bit s v s' h => tbnz_inst_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (r := r) (bit := bit) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3251) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3251, ctor_tcbc_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj1⟩ : Nonempty (ctx.defInst? x = some _) := ⟨‹_›⟩
    obtain ⟨hi1⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clif hctx hj1 hi1
    obtain ⟨hd1⟩ : Nonempty (V.data 152 2 _ = _) := ⟨‹_›⟩
    rw [← hd1] at hdat1
    obtain ⟨ty1, a, b, rfl, he1, hfs1⟩ := instData_binary_inv (cop := .band) variantNames_Band rfl hdat1
    simp only [List.cons.injEq, and_true] at hfs1
    subst hfs1
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj2⟩ : Nonempty (ctx.defInst? b = some _) := ⟨‹_›⟩
    obtain ⟨hd2⟩ : Nonempty (V.data 152 35 _ = _) := ⟨‹_›⟩
    obtain ⟨hi2⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨ty2, imm, rfl, he2, hcl2⟩ := iconst_data_inv hctx hj2 hi2 hd2
    repeat (isel_inv_simp [ctor_tcbc_iff] at * <;> isel_destruct <;> subst_vars)
    have hra := hctx.valueReg a _ ‹ctx.valueReg? a = some _›
    subst hra
    have h667 := ‹ApplyInternal _ _ _ _ 46 667 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kT _ (by omega) _ _ _ _ _ _ _ h667
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
    rw [ofV_tbb_nz] at hmi
    cases hmi
    simp only at hs1 hs2
    rw [hs2, hs1]
    exact ⟨[], _, emitted_emit _ _, rfl⟩
  | _ => simp [termFmt] at hf

set_option maxHeartbeats 4000000 in
/-- **`tbz`** (`rule_lower_3257`). -/
theorem tbz_shape {p : Program} (hp : Data p) : BranchShapeOk p rule_lower_3257 := by
  intro f ctx hctx ti t data targets hd hi _ _ cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kT := fun n (hn : 60 ≤ n) a b r bit s v s' h => tbz_inst_ok hp (ctx := ctx) hc (n := n)
    (a := a) (b := b) (r := r) (bit := bit) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hf := ruleFmt_term hp (r := rule_lower_3257) rfl hp.t2452 term_2452_kind hd hi hmatch
  cases t with
  | brif x tb eb =>
    rw [termData_brif] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3257, ctor_tcbc_iff, ext_fits_in_64_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    have hdat := ‹V.data 152 5 _ = _›
    simp only [V.data.injEq, List.cons.injEq, and_true, true_and] at hdat
    obtain ⟨rfl, rfl⟩ := hdat
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨hj0⟩ : Nonempty (ctx.defInst? x = some _) := ⟨‹_›⟩
    obtain ⟨hi0⟩ : Nonempty (ctx.insts[_]? = some _) := ⟨‹ctx.insts[_]? = some _›⟩
    obtain ⟨cl0, hcl0, hdat0⟩ := ctxInv_clif hctx hj0 hi0
    obtain ⟨hd0⟩ : Nonempty (V.data 152 14 _ = _) := ⟨‹_›⟩
    rw [← hd0] at hdat0
    obtain ⟨cc, tyc, c, z, rfl, rfl, hcc⟩ := instData_icmp_inv hdat0
    have hcc' : cc = .eq := by cases cc <;> simp_all [ccIdx]
    subst hcc'
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨j1, hj1, info1, hi1, hd1⟩ : ∃ j, ctx.defInst? c = some j ∧ ∃ i, ctx.insts[j]? = some i ∧
      V.data 152 2 _ = i.data := ⟨_, ‹_›, _, ‹_›, ‹_›⟩
    obtain ⟨j3, hj3, info3, hi3, hd3⟩ : ∃ j, ctx.defInst? z = some j ∧ ∃ i, ctx.insts[j]? = some i ∧
      V.data 152 35 _ = i.data := ⟨_, ‹_›, _, ‹_›, ‹_›⟩
    obtain ⟨ty3, imm0, rfl, he3, hcl3⟩ := iconst_data_inv hctx hj3 hi3 hd3
    obtain ⟨cl1, hcl1, hdat1⟩ := ctxInv_clif hctx hj1 hi1
    rw [← hd1] at hdat1
    obtain ⟨ty1, a, b, rfl, he1, hfs1⟩ := instData_binary_inv (cop := .band) variantNames_Band rfl hdat1
    simp only [List.cons.injEq, and_true] at hfs1
    subst hfs1
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    obtain ⟨j2, hj2, info2, hi2, hd2⟩ : ∃ j, ctx.defInst? b = some j ∧ ∃ i, ctx.insts[j]? = some i ∧
      V.data 152 35 _ = i.data := ⟨_, ‹_›, _, ‹_›, ‹_›⟩
    obtain ⟨ty2, imm, rfl, he2, hcl2⟩ := iconst_data_inv hctx hj2 hi2 hd2
    repeat (isel_inv_simp [ctor_tcbc_iff, ext_fits_in_64_iff] at * <;> isel_destruct <;> subst_vars)
    have hra := hctx.valueReg a _ ‹ctx.valueReg? a = some _›
    subst hra
    have h668 := ‹ApplyInternal _ _ _ _ 46 668 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kT _ (by omega) _ _ _ _ _ _ _ h668
    have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
    rw [ofV_tbb_z] at hmi
    cases hmi
    simp only at hs1 hs2
    rw [hs2, hs1]
    exact ⟨[], _, emitted_emit _ _, rfl⟩
  | _ => simp [termFmt] at hf

/-! ## `br_table` -/

set_option maxHeartbeats 8000000 in
/-- **`br_table`** (`rule_lower_3277`): `emit_island`, the index extension, the bound check,
`jt_sequence`. -/
theorem brTable_shape {p : Program} (hp : Data p) : BranchShapeOk p rule_lower_3277 := by
  intro f ctx hctx ti t data targets hd hi hbt htl cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 400 := ⟨n - 400, by omega⟩
  have kS := fun n (hn : 60 ≤ n) i s v s' h => side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kI := fun n (hn : 30 ≤ n) k s v s' h => emit_island_ok hp (ctx := ctx) hc (n := n)
    (k := k) (s := s) (v := v) (s' := s') hn h
  have kZ := fun n (hn : 40 ≤ n) x s v s' h => zext32_ok hp (ctx := ctx) hc (n := n)
    (x := x) (s := s) (v := v) (s' := s') hn h
  have kB := fun n (hn : 300 ≤ n) k r d ts s v s' hk hr h => br_table_impl_ok hp (ctx := ctx) hc
    refines_ispec (n := n) (k := k) (r := r) (d := d) (ts := ts) (s := s) (v := v) (s' := s') hn hk
    hr h
  have hf := ruleFmt_term hp (r := rule_lower_3277) rfl hp.t2451 term_2451_kind hd hi hmatch
  cases t with
  | brTable x dc tbl =>
    rw [termData_brTable] at hd; cases hd
    cases hp
    brif_inv [*, rule_lower_3277, ext_jump_table_targets_iff, ctor_jump_table_size_iff,
      ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at hmatch heval
    simp only [hi, Option.some.injEq] at *
    isel_destruct; subst_vars
    repeat (isel_inv_simp [ext_jump_table_targets_iff, ctor_jump_table_size_iff,
      ctor_targets_jt_space_iff, ctor_u32_into_u64_iff] at * <;> isel_destruct <;> subst_vars)
    rename LState => st
    obtain ⟨⟨wx, hwx, hTx⟩, htbl⟩ := hbt _ _ _ rfl
    have hlen := htl _ _ _ rfl
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    have h669 := ‹ApplyInternal _ _ _ _ 46 669 _ _ _ _›
    obtain ⟨hs1, rfl⟩ := kI _ (by omega) _ _ _ _ h669
    have h243 := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
    obtain ⟨mi, hmi, hs2, -⟩ := kS _ (by omega) _ _ _ _ h243
    rw [show ∀ n : Nat, (4 * (8 + (n : Int))) = ((4 * (8 + n) : Nat) : Int) from
      fun n => by push_cast; omega, ofV_emitIsland] at hmi
    cases hmi
    have h556 := ‹ApplyInternal _ _ _ _ 27 556 _ _ _ _›
    have hext := kZ _ (by omega) _ _ _ _ h556
    rw [hs2, hs1] at hext
    obtain ⟨k, msx, rfl, hFx, hkl, -, -⟩ := ExtOut.sem refines_ispec hctx
      (pass := [.int 32, .int 64]) (by exact hvb) (.inl rfl) (by simp) (fun _ => by simp) hext
    have h670 := ‹ApplyInternal _ _ _ _ 13 670 _ _ _ _›
    have hJ := kB _ (by omega) _ _ _ _ _ _ _ (by omega) hkl h670
    simp only at hJ
    obtain ⟨ms0, st2, t1, t2, hF0, rfl, -⟩ := hJ
    have hFall := ((Frag.emit_nodef _ (m := .emitIsland _) rfl).append hFx).append hF0
    exact ⟨_, _, emitted_emit_of_frag hFall _, rfl⟩
  | _ => simp [termFmt] at hf

/-! ## From the rules to the driver's calls -/

/-- **`lower` on a `return`/`trap`** appends a non-empty list of instructions. -/
theorem termShape_runTerm {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    {t : Clif.Terminator} {data : V} (hrt : retOrTrap t = true) (hd : termData t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {st : LState} {out : V} {st' : LState}
    {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower" [.inst ti] st = .ok (some out, st', tr)) : TermShape st st' := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_rule h
  cases hroot : termRootRule r
  · exact absurd hmatch (termUnmatchable r hr hroot f ctx hctx ti t data hrt hd hi {} m (st, #[])
      env' s1)
  · simp only [termRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
    rcases hroot with e | e
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2237 (by rw [e]; rfl)] at hfirst hmatch heval
      exact trap_shape data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2574 (by rw [e]; rfl)] at hfirst hmatch heval
      exact ret_shape data_program f ctx hctx ti t data hrt hd hi {} rfl m n st #[] env' s1 out
        st' tr2 hm hn hvb hfirst hmatch heval

/-- **`lower_branch` on a branch** appends a non-empty list of instructions, the last one
targeting the branch's labels. -/
theorem branchShape_runTerm {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    {t : Clif.Terminator} {data : V} {targets : List Label} (hrt : retOrTrap t = false)
    (hd : termData t = .ok data) (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩)
    (hbt : BrIdxTyped ctx t) (htl : TargetsLen t targets) {st : LState} {out : V} {st' : LState}
    {tr : List RuleId} (hvb : ValsBelow ctx st)
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    BranchShape st st' targets := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, hfirst, hmatch, heval⟩ := runTerm_lower_branch_rule h
  cases hroot : closureRoot r
  · exact absurd hmatch (branchExcludedUnmatchable r hr hroot f ctx hctx ti t data targets hrt hd hi
      {} m (st, #[]) env' s1)
  · have hr' := hr
    rw [show TId.lower_branch = 687 from rfl, data_program.r687] at hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hroot (by decide +kernel)
    · exact tbnz_shape data_program f ctx hctx ti t data targets hd hi hbt htl {} rfl m n st #[]
        env' s1 out st' tr2 hm hn hvb hfirst hmatch heval
    · exact tbz_shape data_program f ctx hctx ti t data targets hd hi hbt htl {} rfl m n st #[]
        env' s1 out st' tr2 hm hn hvb hfirst hmatch heval
    · exact absurd hroot (by decide +kernel)
    · exact absurd hroot (by decide +kernel)
    · exact brif_shape data_program f ctx hctx ti t data targets hd hi hbt htl {} rfl m n st #[]
        env' s1 out st' tr2 hm hn hvb hfirst hmatch heval
    · exact jump_shape data_program f ctx hctx ti t data targets hd hi hbt htl {} rfl m n st #[]
        env' s1 out st' tr2 hm hn hvb hfirst hmatch heval
    · exact brTable_shape data_program f ctx hctx ti t data targets hd hi hbt htl {} rfl m n st #[]
        env' s1 out st' tr2 hm hn hvb hfirst hmatch heval

end Backend.Proof
