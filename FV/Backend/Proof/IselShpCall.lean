import FV.Backend.Proof.IselShpBase
import FV.Backend.Proof.IselCtl

/-!
# Control shapes of the `call` rules of `lower` (`HandOk` of rules 1031, 1032, 1033)

`handOk_call`: the root rules `rule_lower_2508` (`bl name`, 1031), `rule_lower_2518`
(`loadExtNameGot t name; blr t`, 1032) and `rule_lower_2529` (`blr` of the callee value, 1033)
keep `ShpIs`. Their runs (M4's scripts, `call_bl_ruleOk`/`call_got_ruleOk`/`call_ind_ruleOk`,
on a run that returns: `Totality`) emit the stores of the stack-passed arguments (no control
forms), the GOT load of a fresh vreg (`CtlShape.got`) and the call, whose argument registers are
the signature's distinct x0..x8 (`locsOf_regs`, at most one `sret`: `sigAbiOk`) and whose defs
are the fresh vregs of `gen_call_output` in x0..x7 (`callOk_of`). The `call_indirect`'s
signature is covered by `AbiSigsOk` through `indSigs`, given that the instruction is a statement
of `f` (`mem_indSigs`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- `ShpIs` extends over a run that keeps the shapes and does not lower the vreg counter. -/
theorem shpIs_of_since {N : Nat} {s0 s s' : LState} (h : ShpIs N s0 s) (h' : CtlSince N s s')
    (hn : s.nextVreg ≤ s'.nextVreg) : ShpIs N s0 s' := by
  obtain ⟨⟨ms0, he0, hc0⟩, hN⟩ := h
  obtain ⟨ms, he, hc⟩ := h'
  refine ⟨⟨ms0 ++ ms, by rw [he, he0]; simp, fun m hm => ?_⟩, by omega⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact hc0 m hm
  · exact hc m hm

/-- The registers of a call's register-passed arguments are among its locations' registers. -/
theorem regPairsOf_regs : ∀ (locs : List ArgLoc) (args bytes : List Nat),
    ((regPairsOf ((locs.zip args).zip bytes)).map (·.2)).Sublist (locRegs locs)
  | [], _, _ => by simp [regPairsOf]
  | _ :: _, [], _ => by simp [regPairsOf]
  | _ :: _, _ :: _, [] => by simp [regPairsOf]
  | .reg r :: locs, _ :: args, _ :: bytes => by
    simpa [regPairsOf, locRegs] using (regPairsOf_regs locs args bytes).cons_cons r
  | .stack _ :: locs, _ :: args, _ :: bytes => by
    simpa [regPairsOf, locRegs] using regPairsOf_regs locs args bytes

theorem mem_outDefs {b k : Nat} {q : Reg × Nat} (h : q ∈ outDefs b k) :
    ∃ j, j < k ∧ q = (.x j, b + j) := by
  simp only [outDefs, List.mem_map, List.mem_range] at h
  obtain ⟨j, hj, rfl⟩ := h
  exact ⟨j, hj, rfl⟩

/-- **`CallOk` of a call of `s`**: the register-passed arguments of `gen_call_args` and the
`k ≤ 8` fresh defs `x_j → b + j` of `gen_call_rets`. -/
theorem callOk_of {N b k : Nat} (hN : N ≤ b) (hk : k ≤ 8) {s : Clif.Signature}
    (hs : sigAbiOk s = true) {locs : List ArgLoc} {S : Nat} (hl : sigArgLocs s = .ok (locs, S))
    (args bytes : List Nat) :
    CallOk N (regPairsOf ((locs.zip args).zip bytes)) (outDefs b k) := by
  have hlocs : locsOf s = locs := by simp [locsOf, hl]
  obtain ⟨hnd, harg⟩ := locsOf_regs (sret_le_of_sigAbiOk hs)
  rw [hlocs] at hnd harg
  have hsub := regPairsOf_regs locs args bytes
  refine ⟨fun q hq => harg _ (hsub.subset (List.mem_map_of_mem (f := (·.2)) hq)),
    hnd.sublist hsub, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨j, hj, rfl⟩ := mem_outDefs hq
    exact ⟨j, by omega, rfl⟩
  · simpa [outDefs, Function.comp_def] using xs_nodup k
  · simp only [outDefs, List.map_map, Function.comp_def]
    exact List.Pairwise.map _ (fun a c h e => h (by omega)) List.nodup_range
  · intro q hq
    obtain ⟨j, -, rfl⟩ := mem_outDefs hq
    simp only
    omega

theorem lookup_mem {β : Type} : ∀ {l : List (Nat × β)} {a : Nat} {b : β},
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by simp [List.lookup] at h
  | (k, v) :: l, a, b, h => by
    by_cases hk : a = k
    · subst hk
      simp [List.lookup] at h
      subst h
      exact List.mem_cons_self ..
    · have hk' : (a == k) = false := by simpa using hk
      simp only [List.lookup, hk'] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem extern_sigAbiOk {f : Clif.Function} (ha : AbiSigsOk f) {fn : Clif.FnRef}
    {ext : Clif.ExtFunc} (h : f.extern? fn = some ext) : sigAbiOk ext.sig = true :=
  ha.1.2 (fn, ext) (lookup_mem h)

/-- The signature of a statement's `call_indirect` is one of `indSigs f`. -/
theorem mem_indSigs {f : Clif.Function} {sig callee : Nat} {args : List Nat}
    {s : Clif.Signature}
    (hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = .callIndirect sig callee args)
    (hs : f.sigDecls.lookup sig = some s) : s ∈ indSigs f := by
  obtain ⟨B, hB, st, hst, he⟩ := hmem
  unfold indSigs
  refine List.mem_flatMap.mpr ⟨B, hB, List.mem_append_left _ (List.mem_filterMap.mpr ⟨st, hst, ?_⟩)⟩
  rw [he]
  exact hs

theorem isCtl_argStores (E : List (Nat × Nat × Nat)) :
    ∀ m ∈ E.map argStore, m.isCtl = false := by
  intro m hm
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
  rfl

theorem total_2508 : totalE program rule_lower_2508.rhs = true := by decide
theorem total_2518 : totalE program rule_lower_2518.rhs = true := by decide
theorem total_2529 : totalE program rule_lower_2529.rhs = true := by decide

theorem since_push {N : Nat} {st s s' : LState} {c : MInst} (h : CtlSince N st s)
    (he : s'.emitted = s.emitted.push c) (hc : c.isCtl = true → CtlShape N c) :
    CtlSince N st s' := by
  obtain ⟨ms, hms, hcs⟩ := h
  refine ⟨ms ++ [c], by rw [he, hms]; simp, fun m hm => ?_⟩
  rcases List.mem_append.mp hm with hm | hm
  · exact hcs m hm
  · rw [List.mem_singleton] at hm
    subst hm
    exact hc

theorem since_stores {N : Nat} {st s : LState} (E : List (Nat × Nat × Nat))
    (h : s.emitted = st.emitted ++ (E.map argStore).toArray) : CtlSince N st s :=
  ⟨_, h, fun m hm hc => by rw [isCtl_argStores E m hm] at hc; cases hc⟩

theorem since_emit {N : Nat} {st s s' : LState} {c : MInst} (h : CtlSince N st s)
    (he : s' = s.emit c) (hc : c.isCtl = true → CtlShape N c) : CtlSince N st s' :=
  since_push h (by rw [he]; rfl) hc

theorem since_congr {N : Nat} {st s s' : LState} (h : CtlSince N st s)
    (he : s'.emitted = s.emitted) : CtlSince N st s' := by
  obtain ⟨ms, hms, hcs⟩ := h
  exact ⟨ms, he.trans hms, hcs⟩

set_option maxHeartbeats 5000000 in
theorem run_2508 {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) (ha : AbiSigsOk f) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {N : Nat} {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hN : N ≤ st.nextVreg)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2508 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2508.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CtlSince N st st' ∧ st.nextVreg ≤ st'.nextVreg := by
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
  have hsig := extern_sigAbiOk ha hext
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
  refine ⟨since_emit (since_stores (stackEnts ((locs.zip args).zip bytes))
    (by rw [hs1]; simp [freshN_emitted])) hs2
    (fun _ => .callSym _ _ _ (callOk_of hN (by simpa using hr8) hsig hl _ _)), ?_⟩
  rw [hs2, hs1]
  simp [LState.emit, freshN_nextVreg] <;> omega

set_option maxHeartbeats 5000000 in
theorem run_2518 {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) (ha : AbiSigsOk f) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {N : Nat} {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n) (hN : N ≤ st.nextVreg)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2518 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2518.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CtlSince N st st' ∧ st.nextVreg ≤ st'.nextVreg := by
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
  have hsig := extern_sigAbiOk ha hext
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
  refine ⟨since_emit (since_congr (since_emit (since_stores (stackEnts ((locs.zip args).zip bytes))
      ?_) hs0 (fun _ => .got _ _ (by omega))) (by rw [hs1])) hs2
    (fun _ => .callReg _ _ _ (callOk_of hN (by simpa using hr8) hsig hl _ _)), ?_⟩
  · simp [LState.fresh, freshN_emitted]
  · rw [hs2, hs1, hs0]
    simp [LState.emit, LState.fresh, freshN_nextVreg] <;> omega

set_option maxHeartbeats 5000000 in
theorem run_2529 {p : Program} (hp : Data p) (hpI : IndData p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
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
    CtlSince N st st' ∧ st.nextVreg ≤ st'.nextVreg := by
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
  refine ⟨since_emit (since_stores (stackEnts ((locs.zip args).zip bytes))
    (by rw [hs1]; simp [freshN_emitted])) hs2
    (fun _ => .callReg _ _ _ (callOk_of hN (by simpa using hr8) hsig hl _ _)), ?_⟩
  rw [hs2, hs1]
  simp [LState.emit, freshN_nextVreg] <;> omega

/-- A rule whose returning runs keep the shapes and do not lower the vreg counter, with a total
right-hand side, is `HandOk`. -/
theorem handOk_of_run (htot : Totality) {ctx : Ctx} {N ii : Nat} {rl : Rule}
    (ht : totalE program rl.rhs = true)
    (hrun : ∀ (cfg : Config), cfg.checkOverlap = false → ∀ (m n : Nat) (st : LState)
      (tr : Array RuleId) (env' : Isle.Interp.Env V) (s1 : LState × Array RuleId) (out : V)
      (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n → N ≤ st.nextVreg →
      (matchRule program (sem ctx) cfg m rl [.inst ii]).run (st, tr) = .ok (some env', s1) →
      (evalExpr program (sem ctx) cfg n rl.rhs env').run s1 = .ok (some out, (st', tr')) →
      CtlSince N st st' ∧ st.nextVreg ≤ st'.nextVreg) :
    HandOk ctx N [.inst ii] rl := by
  intro cfg hco m n s0 st tr env' s1 r st' tr' hm hn hsh hmatch heval
  obtain ⟨out, rfl⟩ := Option.isSome_iff_exists.mp
    (htot.1 ctx cfg n _ env' s1 r (st', tr') ht heval)
  obtain ⟨h1, h2⟩ := hrun cfg hco m n st tr env' s1 out st' tr' hm hn hsh.2 hmatch heval
  exact shpIs_of_since hsh h1 h2

/-- **The `call` rules of `lower` keep `ShpIs`** (rules 1031, 1032, 1033). `hmem`: the
instruction is a statement of `f`, so that a `call_indirect`'s signature is one of `indSigs f`
(`AbiSigsOk`). -/
theorem handOk_call (htot : Totality) {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (ha : Spill.AbiSigsOk f) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hmem : ∃ B ∈ f.blocks, ∃ st ∈ B.body, st.inst = inst) {rl : Rule}
    (hrl : rl ∈ program.rulesOf TId.lower) (hid : rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033)
    (N : Nat) : HandOk ctx N [.inst ii] rl := by
  rcases hid with h | h | h
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2508 (by rw [h]; rfl)
    exact handOk_of_run htot total_2508 fun _ hco _ _ _ _ _ _ _ _ _ hm hn hN =>
      run_2508 data_program hctx ha hi hc hco hm hn hN
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2518 (by rw [h]; rfl)
    exact handOk_of_run htot total_2518 fun _ hco _ _ _ _ _ _ _ _ _ hm hn hN =>
      run_2518 data_program hctx ha hi hc hco hm hn hN
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2529 (by rw [h]; rfl)
    have hsigs : ∀ sig callee args s, inst = .callIndirect sig callee args →
        f.sigDecls.lookup sig = some s → sigAbiOk s = true := fun sig callee args s he hs =>
      (ha.2 s (mem_indSigs (he ▸ hmem) hs)).2
    exact handOk_of_run htot total_2529 fun _ hco _ _ _ _ _ _ _ _ _ hm hn hN =>
      run_2529 data_program indData_program hctx hi hc hsigs hco hm hn hN

end Backend.Proof.Cov
