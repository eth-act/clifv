import FV.Backend.Proof.IselShpTBase
import FV.Backend.Proof.IselShpCall
import FV.Backend.Proof.IselCtlCallTI
import FV.Backend.Proof.LowerContractT
import FV.Backend.Proof.IselCovTCall

/-!
# Control shapes of the `call` rules of `lower` over typed contexts (rules 1031, 1032, 1033)

`IselShpCall` over typed contexts (`CtxT`): the root rules `rule_lower_2508` (`bl name`, 1031),
`rule_lower_2518` (`loadExtNameGot t name; blr t`, 1032) and `rule_lower_2529` (`blr` of the
callee value, 1033) keep the typed invariant `ShpIsT`. The runs emit the stores of the
stack-passed arguments (no control forms), the GOT load of a fresh vreg and the call, whose
argument registers are the signature's distinct `x0..x8` and whose defs are the fresh vregs of
`gen_call_output` in `x0..x7` (the integer `callOk_of`); the ABI returns are integer
(`call_retClassesSigE`: the typed context's integer `call` callees, `CtxT.calls`). The context-independent runs
(`call_impl_ok`, the `ctor_*` facts, `total_*`, `mem_lower_*`) are the integer ones.
-/

namespace Backend.Proof.CovT

open Backend Backend.Proof Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
open Backend.Proof.Cov (total_2508 total_2518 total_2529 callOk_of mem_indSigs isCtl_argStores
  totalE extern_sigAbiOk call_retClassesT)

set_option maxRecDepth 20000

/-! ## Typed helpers -/

/-- `ShpIsT` extends over a run that keeps the typed shapes and does not lower the vreg
counter. -/
theorem shpIsT_of_since {N : Nat} {s0 s s' : LState} (h : ShpIsT N s0 s) (h' : CtlSinceT N s s')
    (hn : s.nextVreg ≤ s'.nextVreg) : ShpIsT N s0 s' := by
  obtain ⟨⟨ms0, he0, hc0⟩, hN⟩ := h
  obtain ⟨ms, he, hc⟩ := h'
  refine ⟨⟨ms0 ++ ms, by rw [he, he0]; simp, fun m hm => ?_⟩, by omega⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact hc0 m hm
  · exact hc m hm

/-- A callee with an integer signature (`Compile.sigE`) returns integers (`call_retClassesT` for
one signature: the typed context's `CtxT.calls`). -/
theorem call_retClassesSigE {e : Clif.ExtFunc} (h : Compile.sigE e.sig = true) :
    (sigRets e.sig).map retClass = List.replicate (sigRets e.sig).length .int := by
  apply sigRets_classes_int
  simp only [Compile.sigE, Compile.tyE, Bool.and_eq_true, List.all_eq_true] at h
  exact List.all_eq_true.mpr fun p hp => (h.2 p hp).1

theorem since_pushT {N : Nat} {st s s' : LState} {c : MInst} (h : CtlSinceT N st s)
    (he : s'.emitted = s.emitted.push c) (hc : c.isCtl = true → CtlShapeT N c) :
    CtlSinceT N st s' := by
  obtain ⟨ms, hms, hcs⟩ := h
  refine ⟨ms ++ [c], by rw [he, hms]; simp, fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact hcs m hm
  · rw [List.mem_singleton] at hm
    subst hm
    exact hc

theorem since_storesT {N : Nat} {st s : LState} (E : List (Nat × Nat × Nat))
    (h : s.emitted = st.emitted ++ (E.map argStore).toArray) : CtlSinceT N st s :=
  ⟨_, h, fun m hm hc => by rw [isCtl_argStores E m hm] at hc; cases hc⟩

theorem since_emitT {N : Nat} {st s s' : LState} {c : MInst} (h : CtlSinceT N st s)
    (he : s' = s.emit c) (hc : c.isCtl = true → CtlShapeT N c) : CtlSinceT N st s' :=
  since_pushT h (by rw [he]; rfl) hc

theorem since_congrT {N : Nat} {st s s' : LState} (h : CtlSinceT N st s)
    (he : s'.emitted = s.emitted) : CtlSinceT N st s' := by
  obtain ⟨ms, hms, hcs⟩ := h
  exact ⟨ms, he.trans hms, hcs⟩

/-! ## The runs -/

set_option maxHeartbeats 5000000 in
theorem run_2508 {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxT f ctx) (ha : AbiSigsOk f)
    (hxi : ∀ fn e, f.extern? fn = some e → e.sig.params.all (·.ty.isInt) = true) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {N : Nat} {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hN : N ≤ st.nextVreg)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2508 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2508.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CtlSinceT N st st' ∧ st.nextVreg ≤ st'.nextVreg := by
  have hci := hctx.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hd := hci.data ii info inst hi hcl
  cases hp
  ctl_inv [*, rule_lower_2508] at hmatch
  have hinfo := ‹ctx.insts[ii]? = some _›
  rw [hi] at hinfo
  cases hinfo
  rw [← ‹V.data 152 6 _ = info.data›] at hd
  obtain ⟨fn, args, ext, rfl, hext, hfs⟩ := instData_call_inv hd
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hsig := extern_sigAbiOk ha hext
  have hrc := call_retClassesSigE (hctx.calls ii info fn args ext hi hcl hext)
  have hint := hxi fn ext hext
  have hfn : ctx.func.extern? fn = some ext := by rw [hci.func]; exact hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2508] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_iff _ _ hrc, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, retRegsC_outRegs,
    outRegs_length, Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, retRegsC_outRegs, outRegs_single,
    outRegs_length, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hops : ∀ x ∈ args, IntPos ctx x := fun x hx => hci.intOps ii info _ hi hcl x hx
  have hrs := mapM_valueRegTI hci hops ‹List.mapM ctx.valueReg? args = some _›
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
  refine ⟨since_emitT (since_storesT (stackEnts ((locs.zip args).zip bytes))
    (by rw [hs1]; simp [freshN_emitted])) hs2
    (fun _ => (CtlShape.callSym _ _ _ (callOk_of hN (by simpa using hr8) hsig hint hl _ _)).toT), ?_⟩
  rw [hs2, hs1]
  simp [LState.emit, freshN_nextVreg] <;> omega

set_option maxHeartbeats 5000000 in
theorem run_2518 {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxT f ctx) (ha : AbiSigsOk f)
    (hxi : ∀ fn e, f.extern? fn = some e → e.sig.params.all (·.ty.isInt) = true) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {N : Nat} {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hN : N ≤ st.nextVreg)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2518 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2518.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CtlSinceT N st st' ∧ st.nextVreg ≤ st'.nextVreg := by
  have hci := hctx.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := ctx) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  have hd := hci.data ii info inst hi hcl
  cases hp
  ctl_inv [*, rule_lower_2518] at hmatch
  have hinfo := ‹ctx.insts[ii]? = some _›
  rw [hi] at hinfo
  cases hinfo
  rw [← ‹V.data 152 6 _ = info.data›] at hd
  obtain ⟨fn, args, ext, rfl, hext, hfs⟩ := instData_call_inv hd
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hsig := extern_sigAbiOk ha hext
  have hrc := call_retClassesSigE (hctx.calls ii info fn args ext hi hcl hext)
  have hint := hxi fn ext hext
  have hfn : ctx.func.extern? fn = some ext := by rw [hci.func]; exact hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2518] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_iff _ _ hrc, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, ctor_box_external_name_iff,
    retRegsC_outRegs, outRegs_length,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, retRegsC_outRegs, outRegs_single,
    outRegs_length, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hops : ∀ x ∈ args, IntPos ctx x := fun x hx => hci.intOps ii info _ hi hcl x hx
  have hrs := mapM_valueRegTI hci hops ‹List.mapM ctx.valueReg? args = some _›
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
  refine ⟨since_emitT (since_congrT (since_emitT (since_storesT (stackEnts ((locs.zip args).zip bytes))
      ?_) hs0 (fun _ => (CtlShape.got _ _ (by omega)).toT)) (by rw [hs1])) hs2
    (fun _ => (CtlShape.callReg _ _ _ (callOk_of hN (by simpa using hr8) hsig hint hl _ _)).toT), ?_⟩
  · simp [LState.fresh, freshN_emitted]
  · rw [hs2, hs1, hs0]
    simp [LState.emit, LState.fresh, freshN_nextVreg] <;> omega

set_option maxHeartbeats 5000000 in
theorem run_2529 {p : Program} (hp : Data p) (hpI : IndData p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxT f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst)
    (hsigs : ∀ sig callee args s, inst = .callIndirect sig callee args →
      f.sigDecls.lookup sig = some s → sigAbiOk s = true) {N : Nat} {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hN : N ≤ st.nextVreg)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2529 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2529.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CtlSinceT N st st' ∧ st.nextVreg ≤ st'.nextVreg := by
  have hci := hctx.inv
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have hd := hci.data ii info inst hi hcl
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
  have hint := (sigIntB_iff.mp (instData_callIndirect_int hd hs)).1
  have hrc := sigRets_classes_int (sigIntB_iff.mp (instData_callIndirect_int hd hs)).2
  have hops : ∀ x ∈ callee :: args, IntPos ctx x := fun x hx => hci.intOps ii info _ hi hcl x hx
  simp only [ext_value_list_slice_iff, ext_value_slice_unwrap_iff] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2529] at heval
  isel_destruct; subst_vars
  simp only [ext_value_slice_unwrap_iff, List.cons.injEq, and_true] at *
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_iff _ _ hrc, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, ctor_put_in_reg_iff,
    retRegsC_outRegs, outRegs_length,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, retRegsC_outRegs, outRegs_single,
    outRegs_length, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegTI hci (fun x hx => hops x (List.mem_cons_of_mem _ hx))
    ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hci.valueReg_int ‹ctx.valueReg? callee = some _› (hops callee List.mem_cons_self)
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
  refine ⟨since_emitT (since_storesT (stackEnts ((locs.zip args).zip bytes))
    (by rw [hs1]; simp [freshN_emitted])) hs2
    (fun _ => (CtlShape.callReg _ _ _ (callOk_of hN (by simpa using hr8) hsig hint hl _ _)).toT), ?_⟩
  rw [hs2, hs1]
  simp [LState.emit, freshN_nextVreg] <;> omega

/-! ## The hand-checked rules -/

/-- A rule whose returning runs keep the typed shapes and do not lower the vreg counter, with a
total right-hand side, is `HandOkT`. -/
theorem handOk_of_run (htot : Cov.Totality) {ctx : Ctx} {N ii : Nat} {rl : Rule}
    (ht : totalE program rl.rhs = true)
    (hrun : ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (m n : Nat) (st : LState)
      (tr : Array RuleId) (env' : Isle.Interp.Env V) (s1 : LState × Array RuleId) (out : V)
      (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → N ≤ st.nextVreg →
      (matchRule program (sem ctx) cfg m rl [.inst ii]).run (st, tr) = .ok (some env', s1) →
      (evalExpr program (sem ctx) cfg n rl.rhs env').run s1 = .ok (some out, (st', tr')) →
      CtlSinceT N st st' ∧ st.nextVreg ≤ st'.nextVreg) :
    HandOkT ctx N [.inst ii] rl := by
  intro cfg hco m n s0 st tr env' s1 r st' tr' hm hn hsh hmatch heval
  obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
    (htot.1 ctx cfg n _ env' s1 r (st', tr') ht heval)
  obtain ⟨h1, h2⟩ := hrun cfg hco m n st tr env' s1 out st' tr' hm hn hsh.2 hmatch heval
  exact shpIsT_of_since hsh h1 h2

/-- **The `call` rules of `lower` keep the typed invariant** (rules 1031, 1032, 1033).
`hmem`: the instruction is a statement of `f`, so that a `call_indirect`'s signature is one of
`indSigs f` (`AbiSigsOk`); `hxi`: the externs take integer parameters (subset E:
the typed `call` puts an `f32`/`f64` argument in a V register). -/
theorem handOkT_call (htot : Cov.Totality) {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx)
    (ha : Spill.AbiSigsOk f)
    (hxi : ∀ fn e, f.extern? fn = some e → e.sig.params.all (·.ty.isInt) = true) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst) {rl : Rule}
    (hrl : rl ∈ program.rulesOf TId.lower) (hid : rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033)
    (N : Nat) : HandOkT ctx N [.inst ii] rl := by
  rcases hid with h | h | h
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2508 (by rw [h]; rfl)
    exact handOk_of_run htot total_2508 fun _ hco _ _ _ _ _ _ _ _ _ hm hn hN =>
      run_2508 data_program hctx ha hxi hi hc hco hm hn hN
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2518 (by rw [h]; rfl)
    exact handOk_of_run htot total_2518 fun _ hco _ _ _ _ _ _ _ _ _ hm hn hN =>
      run_2518 data_program hctx ha hxi hi hc hco hm hn hN
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2529 (by rw [h]; rfl)
    have hsigs : ∀ sig callee args s, inst = .callIndirect sig callee args →
        f.sigDecls.lookup sig = some s → sigAbiOk s = true := fun sig callee args s he hs =>
      ha.2 s (mem_indSigs (he ▸ hmem) hs)
    exact handOk_of_run htot total_2529 fun _ hco _ _ _ _ _ _ _ _ _ hm hn hN =>
      run_2529 data_program indData_program hctx hi hc hsigs hco hm hn hN

end Backend.Proof.CovT
