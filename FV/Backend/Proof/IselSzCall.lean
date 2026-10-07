import FV.Backend.Proof.IselSzDefs
import FV.Backend.Proof.IselShpCall
import FV.Backend.Proof.IselShpTry
import FV.Backend.Proof.IselShpTotal

/-!
# The size of the ISLE lowering's output (V6c): the `call` and `try_call` rules

The hand-checked call rules emit at most `323 + 125 n ≤ szCallB n` (`HandW` with `wtA`), for a
call with `n` arguments:

* `handW_call`: the root rules of `lower` on a `call`/`call_indirect` (`rule_lower_2508`, `bl`,
  1031; `rule_lower_2518`, GOT + `blr`, 1032; `rule_lower_2529`, `blr` of the callee value,
  1033);
* `handW_try`: the root rules of `lower_branch` on a `try_call`/`try_call_indirect`
  (`rule_lower_2542`, 1034; `rule_lower_2551`, 1035; `rule_lower_2561`, 1036), in the driver's
  `try_call` context.

The runs (the scripts of `IselShpCall`/`IselShpTry`, on a run that returns: `totality`) emit the
stores of the stack-passed arguments (`argStore`, weight 105 each), for 1032/1035 a
`loadExtNameGot` (102), and the call, whose uses are the register-passed arguments and whose defs
are at most 8 (`retRegs`; for a `try_call`, `tryDefs_eq`'s `max n 2`): weight
`1 + 20 · (1 + uses + defs)`. The stack-passed and register-passed arguments together are at most
the arguments (`stackEnts_add_regPairsOf`): `181 + 125 n`, plus 102 for the GOT load.
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The weight of the emitted code -/

/-- A call's arguments are stack-passed or register-passed. -/
theorem stackEnts_add_regPairsOf : ∀ (T : List ((ArgLoc × Nat) × Nat)),
    (stackEnts T).length + (regPairsOf T).length = T.length
  | [] => rfl
  | ((l, _), _) :: T => by
    have ih := stackEnts_add_regPairsOf T
    cases l <;> simp only [stackEnts, regPairsOf, List.filterMap_cons, List.length_cons,
      List.length_cons] at ih ⊢ <;> omega

private theorem wtA_append' (a : Array MInst) (ms : List MInst) :
    wtA (a ++ ms.toArray) = wtA a + wtL ms := by
  simp [wtA, wtL, List.map_append, List.sum_append]

private theorem wtA_push' (a : Array MInst) (m : MInst) : wtA (a.push m) = wtA a + szInstW m := by
  simp [wtA, wtL, List.map_append, List.sum_append]

theorem wtL_argStores : ∀ (E : List (Nat × Nat × Nat)), wtL (E.map argStore) = 105 * E.length
  | [] => rfl
  | e :: E => by
    have ih := wtL_argStores E
    simp only [wtL, List.map_map, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]
    show 105 + _ = _
    omega

theorem szInstW_call (dst : CallDest) (U : List (Reg × Reg)) (D : List (Reg × Reg)) :
    szInstW (.call ⟨dst, U, D⟩) = 1 + 20 * (1 + U.length + D.length) := rfl

theorem szInstW_got (r : Reg) (nm : String) : szInstW (.loadExtNameGot r nm) = 102 := rfl

/-- **The weight of a call's code**: the stores of its stack-passed arguments, then the call with
its register-passed arguments and at most 8 defs. -/
theorem wt_stores_call {locs : List ArgLoc} {args bytes : List Nat} {dst : CallDest}
    {D : List (Reg × Nat)} (hD : D.length ≤ 8) :
    wtL ((stackEnts ((locs.zip args).zip bytes)).map argStore) +
      szInstW (.call ⟨dst, retPairs (regPairsOf ((locs.zip args).zip bytes)), callDefs D⟩) ≤
      181 + 125 * args.length := by
  rw [wtL_argStores, szInstW_call]
  have h := stackEnts_add_regPairsOf ((locs.zip args).zip bytes)
  have hl : ((locs.zip args).zip bytes).length ≤ args.length := by simp; omega
  simp only [retPairs, callDefs, List.length_map]
  omega

/-- A call's run: its stores, then the call. -/
theorem wt_call_of {st s s' : LState} {locs : List ArgLoc} {args bytes : List Nat}
    {dst : CallDest} {D : List (Reg × Nat)} (hD : D.length ≤ 8)
    (h1 : s.emitted = st.emitted ++ ((stackEnts ((locs.zip args).zip bytes)).map argStore).toArray)
    (h2 : s' = s.emit (.call ⟨dst, retPairs (regPairsOf ((locs.zip args).zip bytes)), callDefs D⟩)) :
    wtA s'.emitted ≤ wtA st.emitted + szCallB args.length := by
  have := wt_stores_call (locs := locs) (args := args) (bytes := bytes) (dst := dst) hD
  rw [h2]
  simp only [LState.emit, wtA_push', h1, wtA_append', szCallB]
  omega

/-- A call's run through the GOT: its stores, the GOT load (after a fresh vreg), then the call. -/
theorem wt_callGot_of {st s0 sG s s' : LState} {locs : List ArgLoc} {args bytes : List Nat}
    {r : Reg} {nm : String} {dst : CallDest} {D : List (Reg × Nat)} (hD : D.length ≤ 8)
    (h0 : s0.emitted = st.emitted ++ ((stackEnts ((locs.zip args).zip bytes)).map argStore).toArray)
    (hg : sG = s0.emit (.loadExtNameGot r nm)) (h1 : s.emitted = sG.emitted)
    (h2 : s' = s.emit (.call ⟨dst, retPairs (regPairsOf ((locs.zip args).zip bytes)), callDefs D⟩)) :
    wtA s'.emitted ≤ wtA st.emitted + szCallB args.length := by
  have := wt_stores_call (locs := locs) (args := args) (bytes := bytes) (dst := dst) hD
  rw [h2]
  simp only [LState.emit, wtA_push', h1, hg, h0, wtA_append', szInstW_got, szCallB]
  omega

/-- `outDefs` has its count's length. -/
theorem outDefs_length (b n : Nat) : (outDefs b n).length = n := by simp [outDefs]

/-! ## The `call` rules of `lower` -/

set_option maxHeartbeats 5000000 in
theorem wrun_2508 {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2508 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2508.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    wtA st'.emitted ≤ wtA st.emitted + stmtSzB inst := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hd := hctx.data ii info inst hi hcl
  cases hp
  ctl_inv [*, rule_lower_2508] at hmatch
  have hinfo := ‹ctx.insts[ii]? = some _›
  rw [hi] at hinfo
  cases hinfo
  rw [← ‹V.data 152 6 _ = info.data›] at hd
  obtain ⟨fn, args, ext, rfl, hext, hfs⟩ := instData_call_inv hd
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2508] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_iff, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, outRegs_single, outRegs_length,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_gen _ _ _ hb hl,
    ctor_gen_call_info_gen _ _ _ _ _ _ _ hl,
    mapM_single_map, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_call] at hmi
  cases hmi
  rw [callDefs_outDefs] at hs2
  exact wt_call_of (by rw [outDefs_length]; simpa using hr8)
    (by rw [hs1]; simp [freshN_emitted]) hs2

set_option maxHeartbeats 5000000 in
theorem wrun_2518 {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2518 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2518.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    wtA st'.emitted ≤ wtA st.emitted + stmtSzB inst := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := ctx) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  have hd := hctx.data ii info inst hi hcl
  cases hp
  ctl_inv [*, rule_lower_2518] at hmatch
  have hinfo := ‹ctx.insts[ii]? = some _›
  rw [hi] at hinfo
  cases hinfo
  rw [← ‹V.data 152 6 _ = info.data›] at hd
  obtain ⟨fn, args, ext, rfl, hext, hfs⟩ := instData_call_inv hd
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2518] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_iff, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, ctor_box_external_name_iff,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, outRegs_single, outRegs_length,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  have h570 := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  obtain ⟨rfl, hs0⟩ := kL _ (by omega) _ _ _ _ _ h570
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  rw [callDefs_outDefs] at hs2
  exact wt_callGot_of (by rw [outDefs_length]; simpa using hr8)
    (by simp [LState.fresh, freshN_emitted]) hs0 (by rw [hs1]) hs2

set_option maxHeartbeats 5000000 in
theorem wrun_2529 {p : Program} (hp : Data p) (hpI : IndData p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2529 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2529.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    wtA st'.emitted ≤ wtA st.emitted + stmtSzB inst := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hd := hctx.data ii info inst hi hcl
  cases hp
  obtain ⟨t196, t2293, t2454⟩ := hpI
  ctl_inv [*, rule_lower_2529, ext_value_slice_unwrap_iff] at hmatch
  have hinfo := ‹ctx.insts[ii]? = some _›
  rw [hi] at hinfo
  cases hinfo
  rw [← ‹V.data 152 7 _ = info.data›] at hd
  obtain ⟨sig, callee, args, s, rfl, hs, hfs⟩ := instData_callIndirect_inv hd
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  simp only [ext_value_list_slice_iff, ext_value_slice_unwrap_iff] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2529] at heval
  isel_destruct; subst_vars
  simp only [ext_value_slice_unwrap_iff, List.cons.injEq, and_true] at *
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_iff, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, ctor_put_in_reg_iff,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, outRegs_single, outRegs_length,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg _ _ ‹ctx.valueReg? callee = some _›
  subst htgt
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  rw [callDefs_outDefs] at hs2
  exact wt_call_of (by rw [outDefs_length]; simpa using hr8)
    (by rw [hs1]; simp [freshN_emitted]) hs2

/-- A rule whose returning runs grow `wtA` by at most `c`, with a total right-hand side, is
`HandW` (`totality`). -/
theorem handW_of_run {ctx : Ctx} {vs : List V} {rl : Rule} {c : Nat}
    (ht : totalE program rl.rhs = true)
    (hrun : ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (m n : Nat) (st : LState)
      (tr : Array RuleId) (env' : Isle.Interp.Env V) (s1 : LState × Array RuleId) (out : V)
      (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
      (matchRule program (sem ctx) cfg m rl vs).run (st, tr) = .ok (some env', s1) →
      (evalExpr program (sem ctx) cfg n rl.rhs env').run s1 = .ok (some out, (st', tr')) →
      wtA st'.emitted ≤ wtA st.emitted + c) :
    HandW program ctx vs rl (fun s => wtA s.emitted) c := by
  intro cfg hco m n st tr env' s1 r st' tr' hm hn hmatch heval
  obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
    (totality.1 ctx cfg n _ env' s1 r (st', tr') ht heval)
  exact hrun cfg hco m n st tr env' s1 out st' tr' hm hn hmatch heval

/-- **The weight of the `call` rules of `lower`** (rules 1031, 1032, 1033): at most
`szCallB` of the call's arguments (`stmtSzB`). -/
theorem handW_call {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower)
    (hid : rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033) :
    HandW program ctx [.inst ii] rl (fun s => wtA s.emitted) (stmtSzB inst) := by
  rcases hid with h | h | h
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2508 (by rw [h]; rfl)
    exact handW_of_run total_2508 fun _ hco _ _ _ _ _ _ _ _ _ hm hn =>
      wrun_2508 data_program hctx hi hc hco hm hn
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2518 (by rw [h]; rfl)
    exact handW_of_run total_2518 fun _ hco _ _ _ _ _ _ _ _ _ hm hn =>
      wrun_2518 data_program hctx hi hc hco hm hn
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2529 (by rw [h]; rfl)
    exact handW_of_run total_2529 fun _ hco _ _ _ _ _ _ _ _ _ hm hn =>
      wrun_2529 data_program indData_program hctx hi hc hco hm hn

/-! ## The `try_call` rules of `lower_branch` -/

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2542` (`bl`, id 1034) on a `try_call`. -/
theorem wtry_bl {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInv f c) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState}
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩)
    (htr : tryRegsOf sig lo = some (c.tryRegs, st1)) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2542 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2542.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    wtA st'.emitted ≤ wtA st.emitted + szCallB args.length := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : c.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  ctl_inv [*, rule_lower_2542, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff] at * <;>
    isel_destruct <;> subst_vars)
  have hx' := ‹c.func.extern? fn = some _›
  rw [hctx.func, hext] at hx'
  cases hx'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor c T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor c T.gen_call_args _ _ = _›
  have hrs := mapM_valueReg hctx ‹List.mapM c.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_call] at hmi
  cases hmi
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
  rw [htrs, exnTableOpnd_cc he, tryDefs_eq _ _ hr8] at hs2
  have hcd : ((List.range (max (sigRets ext.sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  exact wt_call_of (by rw [outDefs_length]; omega) (by rw [hs1]) hs2

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2551` (GOT + `blr`, id 1035) on a `try_call`. -/
theorem wtry_got {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInv f c) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState}
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩)
    (htr : tryRegsOf sig lo = some (c.tryRegs, st1)) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2551 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2551.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    wtA st'.emitted ≤ wtA st.emitted + szCallB args.length := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := c) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : c.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  ctl_inv [*, rule_lower_2551, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff, ctor_box_external_name_iff] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff,
    ctor_box_external_name_iff] at * <;> isel_destruct <;> subst_vars)
  have hx' := ‹c.func.extern? fn = some _›
  rw [hctx.func, hext] at hx'
  cases hx'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor c T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor c T.gen_call_args _ _ = _›
  have hrs := mapM_valueReg hctx ‹List.mapM c.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  have h570 := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  obtain ⟨rfl, hs0⟩ := kL _ (by omega) _ _ _ _ _ h570
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
  rw [htrs, exnTableOpnd_cc he, tryDefs_eq _ _ hr8] at hs2
  have hcd : ((List.range (max (sigRets ext.sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs0 hs1 hs2
  exact wt_callGot_of (by rw [outDefs_length]; omega)
    (by simp [LState.emit, LState.fresh, freshN_emitted]) hs0 (by rw [hs1]) hs2

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2561` (`blr` of the callee value, id 1036) on a `try_call_indirect`. -/
theorem wtry_ind {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) {f : Clif.Function} {c : Ctx} (hctx : CtxInv f c)
    {ti : Nat} {callee : Nat} {args : List Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items))
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩)
    (htr : tryRegsOf sig lo = some (c.tryRegs, st1)) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2561 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2561.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    wtA st'.emitted ≤ wtA st.emitted + szCallB args.length := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  rw [tryCallIndData_eq he] at hd
  cases hd
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  obtain ⟨t196, t2293, t2454⟩ := hpI
  obtain ⟨t266, t2298, t2475⟩ := hpJ
  ctl_inv [*, rule_lower_2561, ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff, ctor_put_in_reg_iff] at hmatch heval
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff, ext_value_list_slice_iff,
    ctor_put_in_regs_vec_iff, ctor_put_in_reg_iff] at * <;> isel_destruct <;> subst_vars)
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor c T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor c T.gen_call_args _ _ = _›
  have hrs := mapM_valueReg hctx ‹List.mapM c.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg _ _ ‹c.valueReg? callee = some _›
  subst htgt
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
  rw [htrs, exnTableOpnd_cc he, tryDefs_eq _ _ hr8] at hs2
  have hcd : ((List.range (max (sigRets sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  exact wt_call_of (by rw [outDefs_length]; omega) (by rw [hs1]) hs2

/-- **The weight of the `try_call` root rules** (`lower_branch` rules 1034, 1035, 1036, in the
driver's `try_call` context): at most `szCallB` of the call's arguments (`termSzB`). The defs
are `tryRegsOf`'s registers (`htr`): the results and the payload registers, at most 8. -/
theorem handW_try {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {lo st1 : LState} {trs : List Reg × List Reg}
    (ht : IsTryWith t et) (hd : tryCallData f t = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items)) (htr : tryRegsOf sig lo = some (trs, st1))
    {targets : List Label} {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower_branch)
    (hid : rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036) :
    HandW program (tryCtx ctx ti data trs) [.inst ti, .labels targets] rl
      (fun s => wtA s.emitted) (termSzB t) := by
  intro cfg hc m n s tr env s1 r s2 tr2 hm hn hmatch heval
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { ctxInv_termCtx hctx hph data with }
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  generalize tryCtx ctx ti data trs = c at hctx' hi htr' hmatch heval
  clear htr
  have hsome : ∀ {e : Isle.Expr}, totalE program e = true →
      (evalExpr program (sem c) cfg n e env).run s1 = .ok (r, (s2, tr2)) → ∃ out, r = some out :=
    fun hte h => Option.isSome_iff_exists.mp (totality.1 c cfg n _ env s1 r (s2, tr2) hte h)
  rcases hid with h | h | h
  · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2542 (by rw [h]; rfl)] at hmatch heval
    obtain ⟨out, rfl⟩ := hsome (by decide +kernel) heval
    rcases ht with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
    · exact wtry_bl data_program tryData_program hctx' hd he hi htr' hc hm hn hmatch heval
    · exact absurd hmatch (tryIndUnmatchable _ mem_lower_branch_2542 rfl f c hctx' ti callee args
        et data targets hd hi cfg m (s, tr) env s1)
  · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2551 (by rw [h]; rfl)] at hmatch heval
    obtain ⟨out, rfl⟩ := hsome (by decide +kernel) heval
    rcases ht with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
    · exact wtry_got data_program tryData_program hctx' hd he hi htr' hc hm hn hmatch heval
    · exact absurd hmatch (tryIndUnmatchable _ mem_lower_branch_2551 rfl f c hctx' ti callee args
        et data targets hd hi cfg m (s, tr) env s1)
  · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2561 (by rw [h]; rfl)] at hmatch heval
    obtain ⟨out, rfl⟩ := hsome (by decide +kernel) heval
    rcases ht with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
    · exact absurd hmatch (tryUnmatchable _ mem_lower_branch_2561 rfl f c hctx' ti fn args
        et data targets hd hi cfg m (s, tr) env s1)
    · exact wtry_ind data_program tryData_program indData_program tryIndData_program hctx' hd
        he hi htr' hc hm hn hmatch heval

end Backend.Proof.Cov
