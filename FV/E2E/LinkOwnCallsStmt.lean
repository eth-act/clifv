import FV.E2E.LinkOwnCallsShapeOf

/-!
# The ISLE call inversion of a `call`/`call_indirect` statement (`CallStmtRunHyp`)

The runs of the `call` rules of `lower` (1031 `rule_lower_2508`: `bl name`; 1032
`rule_lower_2518`: `loadExtNameGot t name; blr t`; 1033 `rule_lower_2529`: `blr` of the callee
value) re-done from `IselShpCall` keeping the callee and the arguments: the stores of the
stack-passed arguments, the GOT load, and one call whose operands are `ShapeOf` the registers
`callRegs` of the signature (`shapeOf_gen`). The other rules of `lower` emit no call (the
no-call model of `LinkOwnCallsRun` with the run relation `CallRel`).
-/

namespace E2E.LinkCheck

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The run relation -/

/-- The code emitted from `s` to `s'` has no `tryCall` and only calls of the statement `inst`. -/
def CallRel (f : Clif.Function) (inst : Clif.Inst) (N : Nat) (s s' : LState) : Prop :=
  ∃ ms : List MInst, s'.emitted = s.emitted ++ ms.toArray ∧ NoTry ms ∧
    ∀ c, MInst.call c ∈ ms → RunCall f inst N ms c

theorem runCall_mono {f : Clif.Function} {inst : Clif.Inst} {N : Nat} {ms ms' : List MInst}
    {c : CallInfo} (hs : ∀ m ∈ ms, m ∈ ms') (h : RunCall f inst N ms c) : RunCall f inst N ms' c := by
  rcases h with ⟨fn, args, e, h1, h2, h3, h4⟩ | h
  · refine .inl ⟨fn, args, e, h1, h2, h3, ?_⟩
    rcases h4 with h4 | ⟨t, ht, hd, hm⟩
    · exact .inl h4
    · exact .inr ⟨t, ht, hd, hs _ hm⟩
  · exact .inr h

theorem callRel_refl (f : Clif.Function) (inst : Clif.Inst) (N : Nat) (s : LState) :
    CallRel f inst N s s :=
  ⟨[], by simp, (fun _ _ h => by cases h), (fun _ h => by cases h)⟩

theorem callRel_trans {f : Clif.Function} {inst : Clif.Inst} {N : Nat} {a b c : LState}
    (h1 : CallRel f inst N a b) (h2 : CallRel f inst N b c) : CallRel f inst N a c := by
  obtain ⟨ms, g1, g2, g3⟩ := h1
  obtain ⟨ms', g4, g5, g6⟩ := h2
  refine ⟨ms ++ ms', by simp [g4, g1], fun c' ti hm => ?_, fun c' hm => ?_⟩
  · rcases List.mem_append.mp hm with hm | hm
    · exact g2 c' ti hm
    · exact g5 c' ti hm
  · rcases List.mem_append.mp hm with hm | hm
    · exact runCall_mono (fun m h => List.mem_append_left _ h) (g3 c' hm)
    · exact runCall_mono (fun m h => List.mem_append_right _ h) (g6 c' hm)

theorem callRel_of_noCall {f : Clif.Function} {inst : Clif.Inst} {N : Nat} {s s' : LState}
    (h : NoCallSince s s') : CallRel f inst N s s' := by
  obtain ⟨ms, h1, h2⟩ := h
  refine ⟨ms, h1, fun c ti hm => ?_, fun c hm => ?_⟩
  · have := h2 _ hm
    simp [isCallB] at this
  · have := h2 _ hm
    simp [isCallB] at this

/-- The emitted code of a call rule: stores, then `pre`, then the call. -/
theorem callRel_emit {f : Clif.Function} {inst : Clif.Inst} {N : Nat} {st st' : LState}
    (E : List (Nat × Nat × Nat)) (pre : List MInst) (c : CallInfo)
    (he : st'.emitted = st.emitted ++ (E.map argStore ++ pre ++ [MInst.call c]).toArray)
    (hpre : ∀ m ∈ pre, isCallB m = false)
    (hc : RunCall f inst N (E.map argStore ++ pre ++ [MInst.call c]) c) : CallRel f inst N st st' := by
  refine ⟨_, he, fun c' ti hm => ?_, fun c' hm => ?_⟩
  · simp only [List.mem_append, List.mem_map, List.mem_singleton] at hm
    rcases hm with (⟨e, -, he'⟩ | hm) | hm
    · cases he'
    · have := hpre _ hm
      simp [isCallB] at this
    · cases hm
  · have hcc : c' = c := by
      simp only [List.mem_append, List.mem_map, List.mem_singleton] at hm
      rcases hm with (⟨e, -, he'⟩ | hm) | hm
      · cases he'
      · have := hpre _ hm
        simp [isCallB] at this
      · cases hm; rfl
    subst hcc
    exact hc

/-! ## The `call` rules -/

set_option maxHeartbeats 5000000 in
theorem run_2508_rel {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) (ha : AbiSigsOk f) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {N : Nat} {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hN : N ≤ st.nextVreg)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2508 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2508.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ∃ (E : List (Nat × Nat × Nat)) (nm : String) (L : List (Nat × Reg)) (D : List (Reg × Nat)),
      st'.emitted = st.emitted ++
        (E.map argStore ++ [] ++ [MInst.call ⟨.sym nm, retPairs L, callDefs D⟩]).toArray ∧
      RunCall f inst N (E.map argStore ++ [] ++ [MInst.call ⟨.sym nm, retPairs L, callDefs D⟩])
        ⟨.sym nm, retPairs L, callDefs D⟩ ∧ st.nextVreg ≤ st'.nextVreg := by
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
  have hsig := Cov.extern_sigAbiOk ha hext
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
  have hE := emit_bl (st := st) (stackEnts ((locs.zip args).zip bytes)) _
    (by rw [hs1]; simp [freshN_emitted]) hs2
  exact ⟨_, _, _, _, hE,
    .inl ⟨_, _, _, rfl, ‹f.extern? _ = some _›, shapeOf_gen hl hb _ _ _ _, .inl rfl⟩,
    by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg] <;> omega⟩

set_option maxHeartbeats 5000000 in
theorem run_2518_rel {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) (ha : AbiSigsOk f) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {N : Nat} {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hN : N ≤ st.nextVreg)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2518 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2518.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ∃ (E : List (Nat × Nat × Nat)) (nm : String) (L : List (Nat × Reg)) (k : Nat),
      st'.emitted = st.emitted ++ (E.map argStore ++
        [MInst.loadExtNameGot (.vreg (st.nextVreg + k) .int) nm] ++
        [MInst.call ⟨.reg (.vreg (st.nextVreg + k) .int), retPairs L,
          callDefs (outDefs st.nextVreg k)⟩]).toArray ∧
      RunCall f inst N (E.map argStore ++ [MInst.loadExtNameGot (.vreg (st.nextVreg + k) .int) nm] ++
        [MInst.call ⟨.reg (.vreg (st.nextVreg + k) .int), retPairs L,
          callDefs (outDefs st.nextVreg k)⟩])
        ⟨.reg (.vreg (st.nextVreg + k) .int), retPairs L, callDefs (outDefs st.nextVreg k)⟩ ∧
      st.nextVreg ≤ st'.nextVreg ∧ out = .regsVec (outRegs st k) := by
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
  have hsig := Cov.extern_sigAbiOk ha hext
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
  have hfr : ∀ k (e : Array MInst), (({ freshN st k with emitted := e } : LState).fresh .int).1 =
      .vreg (st.nextVreg + k) .int := fun k e => by
    simp [LState.fresh, freshN_nextVreg]
  rw [hfr, callDefs_outDefs] at hs2
  rw [hfr] at hs0
  have hE := emit_got (st := st) (stackEnts ((locs.zip args).zip bytes)) _ _ _
    (by simp [LState.fresh, freshN_emitted]) hs0 (by rw [hs1]) hs2
  exact ⟨_, _, _, _, hE,
    .inl ⟨_, _, _, rfl, ‹f.extern? _ = some _›, shapeOf_gen hl hb _ _ _ _,
      .inr ⟨_, by omega, rfl, by simp⟩⟩,
    by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh, freshN_nextVreg] <;> omega,
    by first | rfl | simp [outRegs]⟩

set_option maxHeartbeats 5000000 in
theorem run_2529_rel {p : Program} (hp : Data p) (hpI : IndData p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst)
    (hsigs : ∀ sig callee args s, inst = .callIndirect sig callee args →
      f.sigDecls.lookup sig = some s → sigAbiOk s = true) {N : Nat} {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2529 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2529.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    ∃ (E : List (Nat × Nat × Nat)) (x : Nat) (L : List (Nat × Reg)) (D : List (Reg × Nat)),
      st'.emitted = st.emitted ++
        (E.map argStore ++ [] ++ [MInst.call ⟨.reg (.vreg x .int), retPairs L, callDefs D⟩]).toArray ∧
      RunCall f inst N (E.map argStore ++ [] ++
        [MInst.call ⟨.reg (.vreg x .int), retPairs L, callDefs D⟩])
        ⟨.reg (.vreg x .int), retPairs L, callDefs D⟩ ∧ st.nextVreg ≤ st'.nextVreg := by
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
  have hsig := hsigs sig callee args s rfl hs
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
  have hE := emit_bl (st := st) (stackEnts ((locs.zip args).zip bytes)) _
    (by rw [hs1]; simp [freshN_emitted]) hs2
  exact ⟨_, _, _, _, hE,
    .inr ⟨_, _, _, _, rfl, ‹f.sigDecls.lookup _ = some _›, shapeOf_gen hl hb _ _ _ _, _, rfl⟩,
    by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg] <;> omega⟩

end E2E.LinkCheck
