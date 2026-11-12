import FV.Backend.Proof.KillHypT
import FV.Backend.Proof.KillTryDefs
import FV.Backend.Proof.IselCtlUnmatchTI
import FV.Backend.Proof.IselCtlCallTI
import FV.Backend.Proof.LowerShapeOkT

set_option Elab.async false

/-!
# The exact defs of a `try_call`'s call over the typed scope: `tryDefsExactT`

`KillTryDefs.lean` over float-capable contexts. The integer proof used `CtxInv` for the
function and for the argument and callee vregs being integer vregs; over a typed context these
are the `try_call`'s integer-position operands (`TermIntPos`, `termIntPos_of`), so
`mapM_valueRegTI` and `CtxInvT.valueReg_int` give the same registers (`kd_blT`, `kd_gotT`,
`kd_indT` take exactly these facts), and the other `lower_branch` rules are excluded by the typed
checkers (`tryUnmatchableT_program`, `tryIndUnmatchableT_program`).
-/

namespace Backend.Proof.Kill

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.Spill
  Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2542` (`bl`) on a `try_call` whose arguments' registers are integer vregs. -/
theorem kd_blT {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInvT f c)
    {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable} {data : V}
    (hmap : ∀ {rs : List Reg}, args.mapM c.valueReg? = some rs → rs = args.map fun x => Reg.vreg x .int)
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
    TryEm lo.nextVreg sig.returns.length st st' := by
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
  have hrs := hmap ‹List.mapM c.valueReg? args = some _›
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
  refine ⟨(stackEnts ((locs.zip args).zip bytes)).map argStore ++
    [.call ⟨.sym ext.name, retPairs (regPairsOf ((locs.zip args).zip bytes)),
      callDefs (outDefs lo.nextVreg (max ext.sig.returns.length 2))⟩], ?_, ?_⟩
  · rw [hs2, hs1]; simp [LState.emit, freshN_emitted]
  · intro mi hmi c' hc'
    rcases List.mem_append.mp hmi with hmi | hmi
    · exact tryEm_stores hmi c' hc'
    · rw [List.mem_singleton.mp hmi] at hc'
      cases hc'
      rfl

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2551` (GOT + `blr`) on a `try_call` whose arguments' registers are integer
vregs. -/
theorem kd_gotT {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInvT f c)
    {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable} {data : V}
    (hmap : ∀ {rs : List Reg}, args.mapM c.valueReg? = some rs → rs = args.map fun x => Reg.vreg x .int)
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
    TryEm lo.nextVreg sig.returns.length st st' := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
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
  have hrs := hmap ‹List.mapM c.valueReg? args = some _›
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
    [.loadExtNameGot (.vreg σ.nextVreg .int) ext.name,
     .call ⟨.reg (.vreg σ.nextVreg .int), retPairs (regPairsOf ((locs.zip args).zip bytes)),
      callDefs (outDefs lo.nextVreg (max ext.sig.returns.length 2))⟩], ?_, ?_⟩
  · rw [hσ, hs2, hs1, hs0]
    simp only [LState.emit, LState.fresh]
    rw [← Array.toList_inj]
    simp
  · intro mi hmi c' hc'
    rcases List.mem_append.mp hmi with hmi | hmi
    · exact tryEm_stores hmi c' hc'
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmi
      rcases hmi with rfl | rfl
      · cases hc'
      · cases hc'
        rfl

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2561` (`blr` of the callee value) on a `try_call_indirect` whose callee's and
arguments' registers are integer vregs. -/
theorem kd_indT {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) {f : Clif.Function} {c : Ctx}
    {ti : Nat} {callee : Nat} {args : List Nat} {et : Clif.ExnTable} {data : V}
    (hmap : ∀ {rs : List Reg}, args.mapM c.valueReg? = some rs → rs = args.map fun x => Reg.vreg x .int)
    (hcal : ∀ {r : Reg}, c.valueReg? callee = some r → r = .vreg callee .int)
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
    TryEm lo.nextVreg sig.returns.length st st' := by
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
  have hrs := hmap ‹List.mapM c.valueReg? args = some _›
  subst hrs
  have htgt := hcal ‹c.valueReg? callee = some _›
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
  refine ⟨(stackEnts ((locs.zip args).zip bytes)).map argStore ++
    [.call ⟨.reg (.vreg callee .int), retPairs (regPairsOf ((locs.zip args).zip bytes)),
      callDefs (outDefs lo.nextVreg (max sig.returns.length 2))⟩], ?_, ?_⟩
  · rw [hs2, hs1]; simp [LState.emit]
  · intro mi hmi c' hc'
    rcases List.mem_append.mp hmi with hmi | hmi
    · exact tryEm_stores hmi c' hc'
    · rw [List.mem_singleton.mp hmi] at hc'
      cases hc'
      rfl

set_option maxRecDepth 100000 in
/-- **`TryDefsExact` over the float scope.** -/
theorem tryDefsExactTF : TryDefsExactTF := by
  intro f ctx ranges st0 _ hs _ hb ti t et data sig items lo trs st1 targets out s' tr _ hph het hBt
    hd he _ htr h
  have hcT : CtxT f ctx :=
    ⟨ctxInvT_ofF hs hb, (ctxSpec_of hb).instScopeTF hs.subsetTF, callsE_of_externs hs.externsE ctx⟩
  have hctxT' := ctxT_tryRegs (ctxT_termCtx hcT hph data) trs
  have hctx' : CtxInvT f (tryCtx ctx ti data trs) := hctxT'.inv
  have hip : TermIntPos ctx t := by
    obtain ⟨B, hB, rfl⟩ := hBt
    exact termIntPos_ofF hs hb hB
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
  unfold tryCallF at h
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  rcases internal_cases (n := 999999) rfl data_program.t687 term_687_kind rfl happ with
    ⟨-, rfl⟩ | ⟨rl, hrl, m, env, s1, tr1, tr2, hmk, hkm, hmatch, hrhs⟩
  · intro m hm
    simp at hm
  have hlen : 1002 + (program.rulesOf 687).length ≤ 999999 := lower_branch_len
  have hm : 1000 ≤ m := by omega
  have hrl' : rl ∈ program.rulesOf TId.lower_branch := hrl
  have hsome : ∀ {e : Isle.Expr}, totalE program e = true →
      (evalExpr program (sem (tryCtx ctx ti data trs)) {} 999999 e env).run (s1, tr1) =
        .ok (out, (s', tr2)) → ∃ o, out = some o :=
    fun hte h => Option.isSome_iff_exists.mp (totality.1 _ {} 999999 _ env _ out _ hte h)
  have hfin : TryEm lo.nextVreg sig.returns.length { st1 with emitted := #[] } s' →
      ∀ m ∈ s'.emitted.toList, ∀ c, m = .call c →
        c.defs = callDefs (outDefs lo.nextVreg (max sig.returns.length 2)) := by
    rintro ⟨ms, hms, hc⟩ mi hmi
    rw [hms, Array.empty_append] at hmi
    exact hc mi (by simpa using hmi)
  apply hfin
  rcases het with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
  · have hmap : ∀ {rs : List Reg}, args.mapM (tryCtx ctx ti data trs).valueReg? = some rs →
        rs = args.map fun x => Reg.vreg x .int :=
      fun hrs => mapM_valueRegTI hctx' (fun x hx => hip x hx) hrs
    cases hroot : tryRootRule rl with
    | false =>
      exact absurd hmatch (tryUnmatchableT_program rl hrl' hroot f _ hctxT' ti fn args et data
        targets hd hi {} m _ env _)
    | true =>
      simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
      rcases hroot with hid | hid
      · rw [eq_of_mem_of_rid lower_branch_nodup hrl' mem_lower_branch_2542 (by rw [hid]; rfl)]
          at hmatch hrhs
        obtain ⟨o, rfl⟩ := hsome (by decide +kernel) hrhs
        exact kd_blT data_program tryData_program hctx' hmap hd he hi htr' rfl hm (by omega)
          hmatch hrhs
      · rw [eq_of_mem_of_rid lower_branch_nodup hrl' mem_lower_branch_2551 (by rw [hid]; rfl)]
          at hmatch hrhs
        obtain ⟨o, rfl⟩ := hsome (by decide +kernel) hrhs
        exact kd_gotT data_program tryData_program hctx' hmap hd he hi htr' rfl hm (by omega)
          hmatch hrhs
  · have hmap : ∀ {rs : List Reg}, args.mapM (tryCtx ctx ti data trs).valueReg? = some rs →
        rs = args.map fun x => Reg.vreg x .int :=
      fun hrs => mapM_valueRegTI hctx' (fun x hx => hip x (List.mem_cons_of_mem _ hx)) hrs
    have hcal : ∀ {r : Reg}, (tryCtx ctx ti data trs).valueReg? callee = some r →
        r = .vreg callee .int :=
      fun hr => hctx'.valueReg_int hr (hip callee List.mem_cons_self)
    cases hroot : tryIndRootRule rl with
    | false =>
      exact absurd hmatch (tryIndUnmatchableT_program rl hrl' hroot f _ hctxT' ti callee args et
        data targets hd hi {} m _ env _)
    | true =>
      simp only [tryIndRootRule, beq_iff_eq] at hroot
      rw [eq_of_mem_of_rid lower_branch_nodup hrl' mem_lower_branch_2561 (by rw [hroot]; rfl)]
        at hmatch hrhs
      obtain ⟨o, rfl⟩ := hsome (by decide +kernel) hrhs
      exact kd_indT data_program tryData_program indData_program tryIndData_program hmap hcal hd he
        hi htr' rfl hm (by omega) hmatch hrhs

/-- **`TryDefsExact` over the typed scope.** -/
theorem tryDefsExactT : TryDefsExactT := tryDefsExactTF.toT

end Backend.Proof.Kill
