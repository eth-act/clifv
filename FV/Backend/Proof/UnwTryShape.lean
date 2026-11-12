import FV.Backend.Proof.KillTryDefs

/-!
# The exact code of a `try_call`'s rule (S10g, #404)

`tryEmS_run`: in a `try_call`'s `lower_branch` run (the driver's try context, from the state
after `tryRegsOf`, nothing emitted), the emitted code is instructions that are no `call`, then
one call `⟨dst, retPairs L, callDefs (outDefs lo (max n 2))⟩` whose destination is a symbol or an
int vreg (`TryEmS`). The run commits to `rule_lower_2542` (`bl`), `rule_lower_2551` (GOT + `blr`)
or `rule_lower_2561` (`blr` of the callee value) — the other rules never match — and each emits
argument stores (and for 2551 a GOT load) and one call (`sh_bl`, `sh_got`, `sh_ind`: the
inversions of `KillTryDefs`' `kd_bl`, `kd_got`, `kd_ind` with the whole emitted code kept).

`unwCheck`'s completeness (`FV/Link/UnwCheckIn.lean`) reads off this shape the last call, the
call-free prefix, the call's operands and its def constraints.
-/

namespace Backend.Proof.UnwShape

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.Spill
  Backend.Proof.Driver Backend.Proof.Kill Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- **The code a `try_call` rule emits from `s` to `s'`**: instructions that are no call, then
one call to a symbol or an int vreg, with the `try_call` defs `x j ↦ vreg (b + j)`, `j < max n 2`. -/
def TryEmS (b n : Nat) (s s' : LState) : Prop :=
  ∃ (pre : List MInst) (dst : CallDest) (L : List (Nat × Reg)),
    s'.emitted = s.emitted ++
      (pre ++ [MInst.call ⟨dst, retPairs L, callDefs (outDefs b (max n 2))⟩]).toArray ∧
    (∀ m ∈ pre, ∀ ci, m ≠ .call ci) ∧
    ((∃ nm, dst = .sym nm) ∨ ∃ t, dst = .reg (.vreg t .int))

theorem argStores_noCall (E : List (Nat × Nat × Nat)) :
    ∀ m ∈ E.map argStore, ∀ ci, m ≠ .call ci := by
  intro m hm ci he
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
  cases he

/-! ## The rules -/

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2542` (`bl`, id 1034) on a `try_call`: argument stores, then the call. -/
theorem sh_bl {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInv f c)
    {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState}
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
    TryEmS lo.nextVreg sig.returns.length st st' := by
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
  have hsI := exnTableOpnd_int he
  try have hsE : sigIntB ext.sig = true := by first | (rw [hsig]; exact hsI) | exact hsI
  ctl_inv [*, rule_lower_2542, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff hsI] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff hsI, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff] at * <;>
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
  try (simp only [ctor_gen_try_call_rets_iff hsE] at *; isel_destruct; subst_vars)
  try (simp only [ctor_gen_try_call_rets_iff hsI] at *; isel_destruct; subst_vars)
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
  have hcd : ((List.range (max ext.sig.returns.length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max ext.sig.returns.length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine ⟨(stackEnts ((locs.zip args).zip bytes)).map argStore, .sym ext.name,
    regPairsOf ((locs.zip args).zip bytes), ?_, argStores_noCall _, .inl ⟨_, rfl⟩⟩
  rw [hs2, hs1]; simp [LState.emit, freshN_emitted]

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2551` (GOT + `blr`, id 1035) on a `try_call`: argument stores, the GOT load,
then the call. -/
theorem sh_got {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInv f c)
    {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState}
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
    TryEmS lo.nextVreg sig.returns.length st st' := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  -- the start state's counter, under a name the inversion's substitutions keep
  obtain ⟨σ, hσ⟩ : ∃ σ : LState, σ.nextVreg = st.nextVreg := ⟨st, rfl⟩
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
  have hsI := exnTableOpnd_int he
  try have hsE : sigIntB ext.sig = true := by first | (rw [hsig]; exact hsI) | exact hsI
  ctl_inv [*, rule_lower_2551, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff hsI, ctor_box_external_name_iff] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iff hsI, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff,
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
  try (simp only [ctor_gen_try_call_rets_iff hsE] at *; isel_destruct; subst_vars)
  try (simp only [ctor_gen_try_call_rets_iff hsI] at *; isel_destruct; subst_vars)
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
  rw [show ∀ s : LState, (s.fresh .int).1 = .vreg s.nextVreg .int from fun s => rfl] at hs2 hs0
  have hcd : ((List.range (max ext.sig.returns.length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max ext.sig.returns.length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs0 hs1 hs2
  refine ⟨(stackEnts ((locs.zip args).zip bytes)).map argStore ++
    [.loadExtNameGot (.vreg σ.nextVreg .int) ext.name], .reg (.vreg σ.nextVreg .int),
    regPairsOf ((locs.zip args).zip bytes), ?_, ?_, .inr ⟨_, rfl⟩⟩
  · rw [hσ, hs2, hs1, hs0]
    simp only [LState.emit, LState.fresh]
    rw [← Array.toList_inj]
    simp
  · intro mi hmi ci hc'
    rcases List.mem_append.mp hmi with hmi | hmi
    · exact argStores_noCall _ mi hmi ci hc'
    · rw [List.mem_singleton.mp hmi] at hc'
      cases hc'

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2561` (`blr` of the callee value, id 1036) on a `try_call_indirect`: argument
stores, then the call. -/
theorem sh_ind {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
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
    TryEmS lo.nextVreg sig.returns.length st st' := by
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
  have hsI := exnTableOpnd_int he
  try have hsE : sigIntB ext.sig = true := by first | (rw [hsig]; exact hsI) | exact hsI
  ctl_inv [*, rule_lower_2561, ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff hsI, ctor_put_in_reg_iff] at hmatch heval
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff hsI, ext_value_list_slice_iff,
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
  try (simp only [ctor_gen_try_call_rets_iff hsE] at *; isel_destruct; subst_vars)
  try (simp only [ctor_gen_try_call_rets_iff hsI] at *; isel_destruct; subst_vars)
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
  have hcd : ((List.range (max sig.returns.length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max sig.returns.length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine ⟨(stackEnts ((locs.zip args).zip bytes)).map argStore, .reg (.vreg callee .int),
    regPairsOf ((locs.zip args).zip bytes), ?_, argStores_noCall _, .inr ⟨_, rfl⟩⟩
  rw [hs2, hs1]; simp [LState.emit]

/-! ## The driver's run -/

set_option maxRecDepth 100000 in
/-- **The code of a `try_call`'s `lower_branch` run** (as `lowerFunction` runs it: the try
context, from the state after `tryRegsOf`, nothing emitted), when it returns a value. -/
theorem tryEmS_run {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {st0 : LState}
    (hs : LowerScope f) (hb : buildCtx f = .ok (ctx, ranges, st0)) {ti : Nat}
    {t : Clif.Terminator} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {lo : LState} {trs : List Reg × List Reg} {st1 : LState}
    {targets : List Label} {v : V} {s' : LState} {tr : List Isle.RuleId}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) (het : IsTryWith t et)
    (hd : tryCallData f t = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (htr : tryRegsOf sig lo = some (trs, st1))
    (h : tryCallF ctx ti data trs targets { st1 with emitted := #[] } = .ok (some v, s', tr)) :
    TryEmS lo.nextVreg sig.returns.length { st1 with emitted := #[] } s' := by
  have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { ctxInv_termCtx hctx hph data with }
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
  unfold tryCallF at h
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  obtain ⟨rl, hrl, m, env, s1, st, tr2, hmn, hmatch, hrhs, hs'⟩ :=
    applyTerm_internal_some (n := 999999) rfl data_program.t687 term_687_kind rfl happ
  simp only [Prod.mk.injEq] at hs'
  obtain ⟨rfl, -⟩ := hs'
  have hrl' : rl ∈ program.rulesOf TId.lower_branch := hrl
  have hlen : (program.rulesOf TId.lower_branch).length = 8 := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]; rfl
  have hm : 1000 ≤ m := by
    have : (program.rulesOf 687).length = 8 := hlen
    omega
  rcases het with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
  · cases hroot : tryRootRule rl with
    | false =>
      exact absurd hmatch (tryUnmatchable rl hrl' hroot f _ hctx' ti fn args et data targets hd hi
        {} m _ env _)
    | true =>
      simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
      rcases hroot with hid | hid
      · rw [eq_of_mem_of_rid lower_branch_nodup hrl' mem_lower_branch_2542 (by rw [hid]; rfl)]
          at hmatch hrhs
        exact sh_bl data_program tryData_program hctx' hd he hi htr' rfl hm (by omega) hmatch hrhs
      · rw [eq_of_mem_of_rid lower_branch_nodup hrl' mem_lower_branch_2551 (by rw [hid]; rfl)]
          at hmatch hrhs
        exact sh_got data_program tryData_program hctx' hd he hi htr' rfl hm (by omega) hmatch hrhs
  · cases hroot : tryIndRootRule rl with
    | false =>
      exact absurd hmatch (tryIndUnmatchable rl hrl' hroot f _ hctx' ti callee args et data targets
        hd hi {} m _ env _)
    | true =>
      simp only [tryIndRootRule, beq_iff_eq] at hroot
      rw [eq_of_mem_of_rid lower_branch_nodup hrl' mem_lower_branch_2561 (by rw [hroot]; rfl)]
        at hmatch hrhs
      exact sh_ind data_program tryData_program indData_program tryIndData_program hctx' hd he hi
        htr' rfl hm (by omega) hmatch hrhs

end Backend.Proof.UnwShape
