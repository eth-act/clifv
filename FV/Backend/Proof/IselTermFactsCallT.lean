import FV.Backend.Proof.IselTermFactsCall

/-!
# Completeness of `lowerCheckT`: the outgoing area of `call` and `try_call`, typed contexts

`IselTermFactsCall` over float-capable contexts (`CtxInvT`): the `call` rules (1031, 1032) and the
`try_call` rules (1034, 1035) raise the outgoing area to the callee's stack-argument size. The
symbolic executions are `IselTermFactsCall`'s; the arguments' registers are integer vregs because
the arguments are in integer positions (`CtxInvT.intOps` for a `call`, `TermIntPos` for a
`try_call`) rather than because every value is an integer. A `call`'s outputs may be of either
class (typed calls, S11e5a: `ctor_gen_call_output_typed`, `outRegsC_single`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- The registers of values in integer positions are integer vregs. -/
theorem mapM_valueRegI {ctx : Ctx}
    (hvr : ∀ x r, ctx.valueReg? x = some r → IntPos ctx x → r = .vreg x .int) :
    ∀ {xs : List Nat} {rs : List Reg}, (∀ x ∈ xs, IntPos ctx x) → xs.mapM ctx.valueReg? = some rs →
      rs = xs.map fun x => Reg.vreg x .int
  | [], rs, _, h => by simp at h; simp [h]
  | x :: xs, rs, hi, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs, rfl⟩ := h
    rw [hvr x r hr (hi x List.mem_cons_self),
      mapM_valueRegI hvr (fun y hy => hi y (List.mem_cons_of_mem _ hy)) hrs]
    rfl

/-- `gen_call_output`'s registers are single vregs (of the returns' classes). -/
theorem outRegsC_single (st : LState) (cs : List RegClass) :
    (outRegsC st cs).mapM single? =
      some (cs.zipIdx.map fun q => Reg.vreg (st.nextVreg + q.2) q.1) := by
  rw [show outRegsC st cs = (cs.zipIdx.map fun q => Reg.vreg (st.nextVreg + q.2) q.1).map
    (fun r => [r]) by simp [outRegsC, Function.comp_def]]
  exact mapM_single_map _

/-- `CallOutOk` over float-capable contexts. -/
def CallOutOkT (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInvT f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∀ fn args e, inst = .call fn args → f.extern? fn = some e → stackBytes e.sig ≤ st'.outgoing

set_option maxHeartbeats 5000000 in
/-- **`call`, colocated callee** (`rule_lower_2508`), float-capable context. -/
theorem call_bl_outT {p : Program} (hp : Data p) : CallOutOkT p rule_lower_2508 := by
  intro f ctx hctx ii info inst hi hcl cfg hc m n st tr env' s1 out st' tr' hm hn hmatch heval
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
  have hai : ∀ x ∈ args, IntPos ctx x := fun x hx => hctx.intOps ii info _ hi hcl x (by simpa [intArgs])
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2508] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_typed, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, outRegsC_length,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, outRegsC_single, outRegsC_length,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegI (fun x r h hx => hctx.valueReg_int h hx) hai
    ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_gen _ _ _ hb hl,
    ctor_gen_call_info_gen _ _ _ _ _ _ _ hl,
    mapM_single_map, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  try (simp only [ctor_gen_try_call_rets_iff hsE] at *; isel_destruct; subst_vars)
  try (simp only [ctor_gen_try_call_rets_iff hsI] at *; isel_destruct; subst_vars)
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  intro fn0 args0 e0 hinst he0
  injection hinst with h1 h2
  subst h1 h2
  rw [hext] at he0
  cases he0
  rw [hs2, hs1]
  simp [LState.emit, stackBytes, hl]
  omega

set_option maxHeartbeats 5000000 in
/-- **`call` through the GOT** (`rule_lower_2518`), float-capable context. -/
theorem call_got_outT {p : Program} (hp : Data p) : CallOutOkT p rule_lower_2518 := by
  intro f ctx hctx ii info inst hi hcl cfg hc m n st tr env' s1 out st' tr' hm hn hmatch heval
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
  have hai : ∀ x ∈ args, IntPos ctx x := fun x hx => hctx.intOps ii info _ hi hcl x (by simpa [intArgs])
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2518] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_typed, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, ctor_box_external_name_iff,
    outRegsC_length,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, outRegsC_single, outRegsC_length,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegI (fun x r h hx => hctx.valueReg_int h hx) hai
    ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  have h570 := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  obtain ⟨rfl, hs0⟩ := kL _ (by omega) _ _ _ _ _ h570
  try (simp only [ctor_gen_try_call_rets_iff hsE] at *; isel_destruct; subst_vars)
  try (simp only [ctor_gen_try_call_rets_iff hsI] at *; isel_destruct; subst_vars)
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true,
    ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  intro fn0 args0 e0 hinst he0
  injection hinst with h1 h2
  subst h1 h2
  rw [hext] at he0
  cases he0
  rw [hs2, hs1, hs0]
  simp [LState.emit, LState.fresh, stackBytes, hl]
  omega

/-- **`lower` on a `call` of an extern** (float-capable context) raises the outgoing area to the
callee's stack arguments. -/
theorem callOut_runTermT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat}
    {info : IInfo} {fn : Clif.FnRef} {args : List Clif.ValueId} {e : Clif.ExtFunc}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some (.call fn args))
    (he : f.extern? fn = some e) {s : LState} {out : V} {s' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (some out, s', tr)) :
    stackBytes e.sig ≤ s'.outgoing := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, -, hmatch, heval⟩ := runTerm_lower_rule h
  have hdat := instData_call_eq (hctx.data ii info _ hi hc)
  have hok := List.all_eq_true.mp lower_call_fmts r hr
  simp only [callFmtOk] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      beq_iff_eq] at hok
    obtain ⟨⟨hlo, hhi⟩, hid⟩ := hok
    obtain ⟨info', fs, hinfo, hd'⟩ :=
      ruleFmt_match (vs := []) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    rw [hdat] at hd'
    simp only [V.data.injEq, true_and] at hd'
    have h53 : fT = 2453 := by omega
    rcases hid with ((((h | h) | h) | h) | h)
    · exact absurd h53 h
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2508 (by rw [h]; rfl)] at hmatch heval
      exact call_bl_outT data_program f ctx hctx ii info _ hi hc {} rfl m n s #[] env' s1 out s' tr2
        hm hn hmatch heval fn args e rfl he
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2518 (by rw [h]; rfl)] at hmatch heval
      exact call_got_outT data_program f ctx hctx ii info _ hi hc {} rfl m n s #[] env' s1 out s'
        tr2 hm hn hmatch heval fn args e rfl he
    · exact absurd hmatch (returnCall_unmatch hi hdat
        (.inl (eq_of_mem_of_id lower_ids_nodup hr mem_lower_2580 (by rw [h]; rfl))))
    · exact absurd hmatch (returnCall_unmatch hi hdat
        (.inr (eq_of_mem_of_id lower_ids_nodup hr mem_lower_2587 (by rw [h]; rfl))))
  · cases hok

/-! ## `try_call` -/

/-- The parts of `CtxInvT` the `try_call` rules use (which `tryCtx` keeps): the function, and
integer vregs for values in integer positions. -/
structure TryCtxOkT (f : Clif.Function) (ctx : Ctx) : Prop where
  func : ctx.func = f
  valueReg : ∀ x r, ctx.valueReg? x = some r → IntPos ctx x → r = .vreg x .int

/-- `TryOutOk` over contexts with `TryCtxOkT`, on a `try_call` whose arguments are in integer
positions. -/
def TryOutOkT (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), TryCtxOkT f ctx →
  ∀ (ti : Nat) (fn : Clif.FnRef) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (targets : List Label),
  (∀ x ∈ args, IntPos ctx x) →
  tryCallData f (.tryCall fn args et) = .ok data → ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∀ e, f.extern? fn = some e → stackBytes e.sig ≤ st'.outgoing

set_option maxHeartbeats 5000000 in
/-- **`try_call`, colocated callee** (`rule_lower_2542`), integer-position arguments. -/
theorem try_bl_outT {p : Program} (hp : Data p) (hpT : TryData p) : TryOutOkT p rule_lower_2542 := by
  intro f ctx hcx ti fn args et data targets hai hd hi cfg hc m n st tr env' s1 out st' tr' hm hn
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he, hext, hsig⟩ := tryCallData_spec hd
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : ctx.func.extern? fn = some ext := by rw [hcx.func]; exact hext
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
  have hx' := ‹ctx.func.extern? fn = some _›
  rw [hcx.func, hext] at hx'
  cases hx'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegI hcx.valueReg hai ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  try (simp only [ctor_gen_try_call_rets_iff hsE] at *; isel_destruct; subst_vars)
  try (simp only [ctor_gen_try_call_rets_iff hsI] at *; isel_destruct; subst_vars)
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  intro e0 he0
  rw [hext] at he0
  cases he0
  simp only at hs1 hs2
  rw [hs2, hs1]
  simp only [LState.emit, LState.fresh]
  simp [stackBytes, hl]
  try omega

set_option maxHeartbeats 20000000 in
/-- **`try_call` through the GOT** (`rule_lower_2551`), integer-position arguments. -/
theorem try_got_outT {p : Program} (hp : Data p) (hpT : TryData p) :
    TryOutOkT p rule_lower_2551 := by
  intro f ctx hcx ti fn args et data targets hai hd hi cfg hc m n st tr env' s1 out st' tr' hm hn
    hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := ctx) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he, hext, hsig⟩ := tryCallData_spec hd
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : ctx.func.extern? fn = some ext := by rw [hcx.func]; exact hext
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
  have hx' := ‹ctx.func.extern? fn = some _›
  rw [hcx.func, hext] at hx'
  cases hx'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegI hcx.valueReg hai ‹List.mapM ctx.valueReg? args = some _›
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
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  intro e0 he0
  rw [hext] at he0
  cases he0
  simp only at hs0 hs1 hs2
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh]
  simp [stackBytes, hl]
  try omega

/-- **`lower_branch` on a `try_call` of an extern** whose arguments are in integer positions
raises the outgoing area to the callee's stack arguments. -/
theorem tryOut_runTermT {f : Clif.Function} {ctx : Ctx} (hcx : TryCtxOkT f ctx) {ti : Nat}
    {fn : Clif.FnRef} {args : List Clif.ValueId} {et : Clif.ExnTable} {e : Clif.ExtFunc} {data : V}
    (hai : ∀ x ∈ args, IntPos ctx x)
    (hd : tryCallData f (.tryCall fn args et) = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (he : f.extern? fn = some e)
    {targets : List Label} {s : LState} {out : V} {s' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] s = .ok (some out, s', tr)) :
    stackBytes e.sig ≤ s'.outgoing := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, -, hmatch, heval⟩ := runTerm_lower_branch_rule h
  cases hroot : tryRootRule r
  · exact absurd hmatch (try_unmatch hr hroot hd hi)
  · simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
    have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := lower_branch_ids_nodup
    rcases hroot with h | h
    · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2542 (by rw [h]; rfl)] at hmatch heval
      exact try_bl_outT data_program tryData_program f ctx hcx ti fn args et data targets hai hd hi
        {} rfl m n s #[] env' s1 out s' tr2 hm hn hmatch heval e he
    · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2551 (by rw [h]; rfl)] at hmatch heval
      exact try_got_outT data_program tryData_program f ctx hcx ti fn args et data targets hai hd
        hi {} rfl m n s #[] env' s1 out s' tr2 hm hn hmatch heval e he

end Backend.Proof
