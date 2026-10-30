import FV.Backend.Proof.RegallocOperands
import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.IselPrgCtxT
import FV.Backend.Proof.IselCtlUnmatchTI

/-!
# Progress of the ISLE lowering over the typed scope: a `try_call`'s code ends in a call

`tryCall_lastT`: `tryCall_last` (`IselPrgTryLast`) over the typed scope (`PInvT`). The proofs are
V7's over `CtxInvT` (a value's vreg has its type's class, `mapM_valueRegT`), and the other rules
of `lower_branch` never match by the typed `tryUnmatchableT_program`/`tryIndUnmatchableT_program`.
-/

namespace Backend.Proof.Prg

open Backend Backend.Proof Backend.Proof.Flow Backend.Proof.Cov Backend.Proof.Spill
  Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The registers of a list of values of a float-capable context. -/
theorem mapM_valueRegT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) :
    ∀ {xs : List Nat} {rs : List Reg}, xs.mapM ctx.valueReg? = some rs →
      rs = xs.map fun x => Reg.vreg x (valClassOf ctx x)
  | [], rs, h => by simp at h; simp [h]
  | x :: xs, rs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs, rfl⟩ := h
    rw [hctx.valueReg x r hr, mapM_valueRegT hctx hrs]
    rfl

/-- A value in an integer position has an integer vreg class. -/
theorem valClassOf_int {c : Ctx} {x : Nat} (h : IntPos c x) : valClassOf c x = .int := by
  unfold valClassOf
  cases ht : c.valueType? x with
  | none => rfl
  | some t => simp [valClass_of_eCTys (h t ht)]

/-- The registers of a list of values in integer positions. -/
theorem mapM_valueRegTI {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {xs : List Nat}
    (hint : ∀ x ∈ xs, IntPos ctx x) {rs : List Reg} (h : xs.mapM ctx.valueReg? = some rs) :
    rs = xs.map fun x => Reg.vreg x .int := by
  rw [mapM_valueRegT hctx h]
  exact List.map_congr_left fun x hx => by rw [valClassOf_int (hint x hx)]

/-! ## The rules -/

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2542` (`bl`, id 1034) on a `try_call`: the last emitted instruction is a call. -/
theorem try_bl_lastT {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInvT f c) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} (hd : tryCallData f (.tryCall fn args et) = .ok data)
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩) (hint : ∀ x ∈ args, IntPos c x)
    {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2542 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2542.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ∃ ci, st'.emitted.back? = some (.call ci) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig, items, ext, he, hext, hsig⟩ := tryCallData_spec hd
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
  have hrs := mapM_valueRegTI hctx hint ‹List.mapM c.valueReg? args = some _›
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
  simp only at hs2
  rw [hs2]
  simp [LState.emit]

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2551` (GOT + `blr`, id 1035) on a `try_call`: the last emitted instruction is a
call. -/
theorem try_got_lastT {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInvT f c) {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable}
    {data : V} (hd : tryCallData f (.tryCall fn args et) = .ok data)
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩) (hint : ∀ x ∈ args, IntPos c x)
    {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2551 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2551.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ∃ ci, st'.emitted.back? = some (.call ci) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := c) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig, items, ext, he, hext, hsig⟩ := tryCallData_spec hd
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
  have hrs := mapM_valueRegTI hctx hint ‹List.mapM c.valueReg? args = some _›
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
  simp only at hs2
  rw [hs2]
  simp [LState.emit]

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2561` (`blr` of the callee value, id 1036) on a `try_call_indirect`: the last
emitted instruction is a call. -/
theorem try_ind_lastT {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) {f : Clif.Function} {c : Ctx} (hctx : CtxInvT f c)
    {ti : Nat} {callee : Nat} {args : List Nat} {et : Clif.ExnTable} {data : V}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩) (hint : ∀ x ∈ args, IntPos c x)
    (hcint : IntPos c callee) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2561 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2561.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ∃ ci, st'.emitted.back? = some (.call ci) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig, items, he⟩ := tryCallIndData_spec hd
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
  have hrs := mapM_valueRegTI hctx hint ‹List.mapM c.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg _ _ ‹c.valueReg? callee = some _›
  rw [valClassOf_int hcint] at htgt
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
  simp only at hs2
  rw [hs2]
  simp [LState.emit]

/-! ## The driver's `try_call` run -/

private theorem lower_branch_ids_nodupT :
    ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  decide +kernel

set_option maxRecDepth 100000 in
/-- **A `try_call`'s code ends in a call**: a `lower_branch` run of the driver on a
`try_call`/`try_call_indirect` at its placeholder slot `ti` (in the `try_call` context) that
returns a value has emitted a call last. Over a float-capable context whose function's statements
are in the float scope (`hsc`, `Compile.instETF`; S11f). -/
theorem tryCall_lastG {f : Clif.Function} {ctx : Ctx} (hP : PInvTB f ctx)
    (hsc : ∀ c, InstOf f c → Compile.instETF c = true) {ti : Nat}
    {t : Clif.Terminator} (hB : ∃ B ∈ f.blocks, B.term = t) {data : V}
    (hd : tryCallData f t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {trs : List Reg × List Reg}
    {targets : List Label} {s : LState} {v : V} {s' : LState} {tr : List Isle.RuleId}
    (h : Driver.tryCallF ctx ti data trs targets s = .ok (some v, s', tr)) :
    ∃ c, s'.emitted.back? = some (.call c) := by
  have hctx' : CtxInvT f (tryCtx ctx ti data trs) := { ctxInvT_termCtx hP.ctxInv hi data with }
  have hP' := pinv_tryCtxTB hP hi data trs
  have hcT : CtxT f (tryCtx ctx ti data trs) :=
    ⟨hctx', fun ii info inst hii hc => hsc _ (hP'.clifOf ii info inst hii hc),
      callsE_of_externs hP.externsE _⟩
  have hi' : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hi data
  have hti : ∀ x ∈ Compile.termIntOperands t, IntPos (tryCtx ctx ti data trs) x := by
    obtain ⟨B, hB, rfl⟩ := hB
    exact fun x hx t' ht' => hP.termIntOf B hB x hx t' ht'
  unfold tryCallF at h
  obtain ⟨t', tr', ht, happ⟩ := runTerm_apply h
  rw [program_termByName_lower_branch] at ht
  cases ht
  obtain ⟨rl, hrl, m, env, s1, st, tr2, hmn, hmatch, hrhs, hs⟩ :=
    applyTerm_internal_some (n := 999999) rfl data_program.t687 term_687_kind rfl happ
  simp only [Prod.mk.injEq] at hs
  obtain ⟨rfl, -⟩ := hs
  have hrl' : rl ∈ program.rulesOf TId.lower_branch := hrl
  have hlen : (program.rulesOf TId.lower_branch).length = 8 := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]; rfl
  have hm : 1000 ≤ m := by
    have : (program.rulesOf 687).length = 8 := hlen
    omega
  cases t with
  | tryCall fn args et =>
    cases hroot : tryRootRule rl with
    | false =>
      exact absurd hmatch (tryUnmatchableT_program rl hrl' hroot f _ hcT ti fn args et data targets hd hi'
        {} m _ env _)
    | true =>
      simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
      rcases hroot with hid | hid
      · rw [eq_of_mem_of_rid lower_branch_ids_nodupT hrl' mem_lower_branch_2542 (by rw [hid]; rfl)]
          at hmatch hrhs
        exact try_bl_lastT data_program tryData_program hctx' hd hi' (fun x hx => hti x hx) rfl hm
          (by omega) hmatch hrhs
      · rw [eq_of_mem_of_rid lower_branch_ids_nodupT hrl' mem_lower_branch_2551 (by rw [hid]; rfl)]
          at hmatch hrhs
        exact try_got_lastT data_program tryData_program hctx' hd hi' (fun x hx => hti x hx) rfl hm
          (by omega) hmatch hrhs
  | tryCallIndirect callee args et =>
    cases hroot : tryIndRootRule rl with
    | false =>
      exact absurd hmatch (tryIndUnmatchableT_program rl hrl' hroot f _ hcT ti callee args et data targets
        hd hi' {} m _ env _)
    | true =>
      simp only [tryIndRootRule, beq_iff_eq] at hroot
      rw [eq_of_mem_of_rid lower_branch_ids_nodupT hrl' mem_lower_branch_2561 (by rw [hroot]; rfl)]
        at hmatch hrhs
      exact try_ind_lastT data_program tryData_program indData_program tryIndData_program hctx' hd
        hi' (fun x hx => hti x (List.mem_cons_of_mem _ hx)) (hti callee (List.mem_cons_self ..))
        rfl hm (by omega) hmatch hrhs
  | ret vs => simp [tryCallData, throw, throwThe, MonadExceptOf.throw] at hd
  | trap c => simp [tryCallData, throw, throwThe, MonadExceptOf.throw] at hd
  | jump bc => simp [tryCallData, throw, throwThe, MonadExceptOf.throw] at hd
  | brif c a b => simp [tryCallData, throw, throwThe, MonadExceptOf.throw] at hd
  | brTable x d tb => simp [tryCallData, throw, throwThe, MonadExceptOf.throw] at hd
  | returnCall fn args => simp [tryCallData, throw, throwThe, MonadExceptOf.throw] at hd

/-- **A `try_call`'s code ends in a call** over the typed scope (`tryCall_lastG` under
`PInvT`). -/
theorem tryCall_lastT {f : Clif.Function} {ctx : Ctx} (hP : PInvT f ctx) {ti : Nat}
    {t : Clif.Terminator} (hB : ∃ B ∈ f.blocks, B.term = t) {data : V}
    (hd : tryCallData f t = .ok data)
    (hi : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {trs : List Reg × List Reg}
    {targets : List Label} {s : LState} {v : V} {s' : LState} {tr : List Isle.RuleId}
    (h : Driver.tryCallF ctx ti data trs targets s = .ok (some v, s', tr)) :
    ∃ c, s'.emitted.back? = some (.call c) :=
  tryCall_lastG hP.toB (fun c hc => Compile.instETF_of_instET (hP.instET c hc)) hB hd hi h

end Backend.Proof.Prg
