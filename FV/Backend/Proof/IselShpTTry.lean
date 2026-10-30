import FV.Backend.Proof.IselShpTBase
import FV.Backend.Proof.IselShpTry
import FV.Backend.Proof.LowerContractT
import FV.Backend.Proof.IselTermIntPos
import FV.Backend.Proof.IselCtlCallTI
import FV.Backend.Proof.IselCtlUnmatchTI

/-!
# Control shapes of the `try_call` rules over typed contexts (V4)

`IselShpTry` over typed contexts: the `try_call`/`try_call_indirect` root rules of
`lower_branch` (1034, 1035, 1036, in the driver's `try_call` context) keep the typed invariant
`ShpIsT`. The argument and callee values must be in integer positions (`TermIntPos`: the typed
`try_call` passes its arguments in `x` registers), so that the register-passed arguments' vregs
are the integer vregs `gen_call_args` pairs with the locations (`mapM_valueRegTI`,
`CtxInvT.valueReg_int`); the rest are the integer facts (`shpTry_callOk`, `tryDefs_eq`, the
`tryRegsOf`/`tryCallData` oracles, the exclusions `tryUnmatchableT_program`/
`tryIndUnmatchableT_program`).
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Interp
  Isle.Aarch64
open Backend.Proof.Cov (shpTry_callOk shpTry_argStores shpTry_extern_abi totalE)

set_option maxRecDepth 20000

/-! ## Shapes -/

/-- Appending code whose control forms have the typed shapes keeps the invariant. -/
theorem shpTry_extend {N : Nat} {s0 s s' : LState} (h : ShpIsT N s0 s) (ms : List MInst)
    (he : s'.emitted = s.emitted ++ ms.toArray) (hms : ∀ m ∈ ms, m.isCtl = true → CtlShapeT N m)
    (hv : s.nextVreg ≤ s'.nextVreg) : ShpIsT N s0 s' := by
  obtain ⟨⟨ms0, he0, hms0⟩, hN⟩ := h
  refine ⟨⟨ms0 ++ ms, ?_, fun m hm => ?_⟩, by omega⟩
  · rw [he, he0]; simp
  · rcases List.mem_append.mp hm with hm | hm
    · exact hms0 m hm
    · exact hms m hm

/-! ## The rules -/

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2542` (`bl`, id 1034) on a `try_call`. -/
theorem shpTry_bl {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxT f c) (ha : AbiSigsOk f)
    {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState} {N : Nat}
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩) (hlo : N ≤ lo.nextVreg)
    (htr : tryRegsOf sig lo = some (c.tryRegs, st1))
    (hip : ∀ x ∈ args, IntPos c x) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {s0 st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hst : ShpIsT N s0 st)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2542 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2542.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ShpIsT N s0 st' := by
  have hci := hctx.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have hint := (sigIntB_iff.mp (exnTableOpnd_int he)).1
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  have habi := shpTry_extern_abi ha hext
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : c.func.extern? fn = some ext := by rw [hci.func]; exact hext
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
  rw [hci.func, hext] at hx'
  cases hx'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor c T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor c T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegTI hci hip ‹List.mapM c.valueReg? args = some _›
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
  have hcd : ((List.range (max (sigRets ext.sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine shpTry_extend hst ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
    [.call ⟨.sym ext.name, retPairs (regPairsOf ((locs.zip args).zip bytes)),
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2))⟩]) ?_ ?_ ?_
  · rw [hs2, hs1]; simp [LState.emit, freshN_emitted]
  · intro mi hmi hctl
    rcases List.mem_append.mp hmi with hmi | hmi
    · rw [shpTry_argStores _ mi hmi] at hctl; cases hctl
    · rw [List.mem_singleton.mp hmi]
      exact (CtlShape.callSym _ _ _ (shpTry_callOk hlo habi hint hl args bytes hr8)).toT
  · rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg]

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2551` (GOT + `blr`, id 1035) on a `try_call`. -/
theorem shpTry_got {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxT f c) (ha : AbiSigsOk f)
    {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState} {N : Nat}
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩) (hlo : N ≤ lo.nextVreg)
    (htr : tryRegsOf sig lo = some (c.tryRegs, st1))
    (hip : ∀ x ∈ args, IntPos c x) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {s0 st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hst : ShpIsT N s0 st)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2551 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2551.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ShpIsT N s0 st' := by
  have hci := hctx.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have hint := (sigIntB_iff.mp (exnTableOpnd_int he)).1
  -- the start state's counter, under a name the inversion's substitutions keep
  obtain ⟨σ, hσ⟩ : ∃ σ : LState, σ.nextVreg = st.nextVreg := ⟨st, rfl⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := c) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  have habi := shpTry_extern_abi ha hext
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : c.func.extern? fn = some ext := by rw [hci.func]; exact hext
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
  rw [hci.func, hext] at hx'
  cases hx'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor c T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor c T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegTI hci hip ‹List.mapM c.valueReg? args = some _›
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
  have hcd : ((List.range (max (sigRets ext.sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs0 hs1 hs2
  refine shpTry_extend hst ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
    [.loadExtNameGot (.vreg σ.nextVreg .int) ext.name,
     .call ⟨.reg (.vreg σ.nextVreg .int), retPairs (regPairsOf ((locs.zip args).zip bytes)),
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2))⟩]) ?_ ?_ ?_
  · rw [hσ, hs2, hs1, hs0]
    simp only [LState.emit, LState.fresh]
    rw [← Array.toList_inj]
    simp
  · intro mi hmi hctl
    rcases List.mem_append.mp hmi with hmi | hmi
    · rw [shpTry_argStores _ mi hmi] at hctl; cases hctl
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmi
      rcases hmi with rfl | rfl
      · exact (CtlShape.got _ _ (hσ ▸ hst.2)).toT
      · exact (CtlShape.callReg _ _ _ (shpTry_callOk hlo habi hint hl args bytes hr8)).toT
  · rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh]

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2561` (`blr` of the callee value, id 1036) on a `try_call_indirect`. -/
theorem shpTry_ind {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) {f : Clif.Function} {c : Ctx} (hctx : CtxT f c)
    {ti : Nat} {callee : Nat} {args : List Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState} {N : Nat}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items)) (habi : sigAbiOk sig = true)
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩) (hlo : N ≤ lo.nextVreg)
    (htr : tryRegsOf sig lo = some (c.tryRegs, st1))
    (hip : ∀ x ∈ callee :: args, IntPos c x) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {s0 st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hst : ShpIsT N s0 st)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2561 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2561.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ShpIsT N s0 st' := by
  have hci := hctx.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have hint := (sigIntB_iff.mp (exnTableOpnd_int he)).1
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
  ctl_inv [*, rule_lower_2561, ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff hsI, ctor_put_in_reg_iff] at hmatch heval
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff hsI, ext_value_list_slice_iff,
    ctor_put_in_regs_vec_iff, ctor_put_in_reg_iff] at * <;> isel_destruct <;> subst_vars)
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor c T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor c T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegTI hci (fun x hx => hip x (List.mem_cons_of_mem _ hx))
    ‹List.mapM c.valueReg? args = some _›
  subst hrs
  have htgt := hci.valueReg_int ‹c.valueReg? callee = some _› (hip callee List.mem_cons_self)
  subst htgt
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
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
  have hcd : ((List.range (max (sigRets sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine shpTry_extend hst ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
    [.call ⟨.reg (.vreg callee .int), retPairs (regPairsOf ((locs.zip args).zip bytes)),
      callDefs (outDefs lo.nextVreg (max (sigRets sig).length 2))⟩]) ?_ ?_ ?_
  · rw [hs2, hs1]; simp [LState.emit]
  · intro mi hmi hctl
    rcases List.mem_append.mp hmi with hmi | hmi
    · rw [shpTry_argStores _ mi hmi] at hctl; cases hctl
    · rw [List.mem_singleton.mp hmi]
      exact (CtlShape.callReg _ _ _ (shpTry_callOk hlo habi hint hl args bytes hr8)).toT
  · rw [hs2, hs1]; simp [LState.emit]

/-! ## The hand-checked `try_call` rules -/

/-- **The `try_call` root rules keep the typed control-shape invariant** (`lower_branch` rules
1034, 1035, 1036, in the driver's `try_call` context). Beyond the contract: `hind`, the
exception table's signature of a `try_call_indirect` passes the ABI check (as `AbiSigsOk` gives
for the `try_call_indirect`s of `f`'s blocks, `indSigs`); without it the statement is false (two
`sret` parameters put two arguments in x8). `hip`: the `try_call`'s callee and arguments are in
integer positions (`TermIntPos`: the typed `try_call` passes its arguments in `x` registers). -/
theorem handOkT_try (htot : Cov.Totality) {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx)
    (ha : AbiSigsOk f) {ti : Nat} (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩)
    {t : Clif.Terminator} {et : Clif.ExnTable} {data : V} {sig : Clif.Signature}
    {items : List (Option Nat)} {lo st1 : LState} {trs : List Reg × List Reg}
    (ht : IsTryWith t et) (hd : tryCallData f t = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items))
    (hip : TermIntPos ctx t)
    (hind : ∀ callee args, t = .tryCallIndirect callee args et → sigAbiOk sig = true)
    (N : Nat) (hlo : N ≤ lo.nextVreg) (htr : tryRegsOf sig lo = some (trs, st1))
    {targets : List Label} {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower_branch)
    (hid : rl.id = 1034 ∨ rl.id = 1035 ∨ rl.id = 1036) :
    HandOkT (tryCtx ctx ti data trs) N [.inst ti, .labels targets] rl := by
  intro cfg hc m n s0 s tr env s1 r s2 tr2 hm hn hsh hmatch heval
  have hctx' : CtxT f (tryCtx ctx ti data trs) := ctxT_tryRegs (ctxT_termCtx hctx hph data) trs
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  have hsome : ∀ {e : Isle.Expr}, totalE program e = true →
      (evalExpr program (sem (tryCtx ctx ti data trs)) cfg n e env).run s1 =
        .ok (r, (s2, tr2)) → ∃ out, r = some out :=
    fun hte h => Option.isSome_iff_exists.mp
      (htot.1 (tryCtx ctx ti data trs) cfg n _ env s1 r (s2, tr2) hte h)
  rcases hid with h | h | h
  · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2542 (by rw [h]; rfl)] at hmatch heval
    obtain ⟨out, rfl⟩ := hsome (by decide +kernel) heval
    rcases ht with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
    · have hops : ∀ x ∈ args, IntPos (tryCtx ctx ti data trs) x := fun x hx =>
        hip x (by simpa [Compile.termIntOperands] using hx)
      have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
      exact shpTry_bl data_program tryData_program hctx' ha hd he hi hlo htr' hops hc hm hn hsh
        hmatch heval
    · exact absurd hmatch (tryIndUnmatchableT_program _ mem_lower_branch_2542 rfl f _ hctx' ti
        callee args et data targets hd hi cfg m (s, tr) env s1)
  · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2551 (by rw [h]; rfl)] at hmatch heval
    obtain ⟨out, rfl⟩ := hsome (by decide +kernel) heval
    rcases ht with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
    · have hops : ∀ x ∈ args, IntPos (tryCtx ctx ti data trs) x := fun x hx =>
        hip x (by simpa [Compile.termIntOperands] using hx)
      have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
      exact shpTry_got data_program tryData_program hctx' ha hd he hi hlo htr' hops hc hm hn hsh
        hmatch heval
    · exact absurd hmatch (tryIndUnmatchableT_program _ mem_lower_branch_2551 rfl f _ hctx' ti
        callee args et data targets hd hi cfg m (s, tr) env s1)
  · rw [eq_of_mem_of_rid hnd hrl mem_lower_branch_2561 (by rw [h]; rfl)] at hmatch heval
    obtain ⟨out, rfl⟩ := hsome (by decide +kernel) heval
    rcases ht with ⟨fn, args, rfl⟩ | ⟨callee, args, rfl⟩
    · exact absurd hmatch (tryUnmatchableT_program _ mem_lower_branch_2561 rfl f _ hctx' ti fn
        args et data targets hd hi cfg m (s, tr) env s1)
    · have hops : ∀ x ∈ callee :: args, IntPos (tryCtx ctx ti data trs) x := fun x hx =>
        hip x (by simpa [Compile.termIntOperands] using hx)
      have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
      exact shpTry_ind data_program tryData_program indData_program tryIndData_program hctx' hd
        he (hind callee args rfl) hi hlo htr' hops hc hm hn hsh hmatch heval

end Backend.Proof.CovT
