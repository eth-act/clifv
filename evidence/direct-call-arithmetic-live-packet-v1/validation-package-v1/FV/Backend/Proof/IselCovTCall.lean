import FV.Backend.Proof.IselCovCall
import FV.Backend.Proof.IselCtlCallF
import FV.Compile.SubsetT

/-!
# Form coverage over float-capable contexts (typed V3): the `call` rules' results

`IselCovCall`'s `out_call` over `CtxInvT`: with integer externs (`Compile.sigE`, a conjunct of
`Compile.functionET`) a `call`'s callee returns integers (`call_retClassesT`), a
`call_indirect`'s signature is integer (`instData`'s `sigIntB`), so the `call` root rules of
`lower` (1031, 1032, 1033) return int vregs (`IntOut`).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Flow Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- A `call` or `call_indirect`. -/
def CallInst : Clif.Inst → Prop
  | .call .. | .callIndirect .. => True
  | _ => False

/-- With integer externs a `call`'s ABI returns are all of class `int`. -/
theorem call_retClassesT {f : Clif.Function} (hx : f.externs.all (Compile.sigE ·.2.sig) = true)
    {fn : Clif.FnRef} {e : Clif.ExtFunc} (he : f.extern? fn = some e) :
    (sigRets e.sig).map retClass = List.replicate (sigRets e.sig).length .int := by
  apply sigRets_classes_int
  have h := List.all_eq_true.mp hx _ (Compile.lookup_mem he)
  simp only [Compile.sigE, Compile.tyE, Bool.and_eq_true, List.all_eq_true] at h
  exact List.all_eq_true.mpr fun p hp => (h.2 p hp).1

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2508` (`bl`): the results are the int vregs of `gen_call_output` (the callee
returns integers in an integer context, `CtxInv.call_retClasses`). -/
theorem out_2508T {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2508 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2508.rhs env').run s1 =
      .ok (some out, (st', tr'))) : IntOut out ∧ CallInst inst := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
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
  have hrc := call_retClassesT hx hext
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
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
  have hrs := mapM_valueRegC hctx.toCallCtx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_genC _ _ _ (fun x => valClassOf ctx x) hb hl,
    ctor_gen_call_info_gen _ _ _ _ _ _ _ hl,
    mapM_single_map, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  exact ⟨intOut_outRegs _ _, trivial⟩

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2518` (GOT load and `blr`): the results are the int vregs of
`gen_call_output`. -/
theorem out_2518T {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2518 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2518.rhs env').run s1 =
      .ok (some out, (st', tr'))) : IntOut out ∧ CallInst inst := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
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
  have hrc := call_retClassesT hx hext
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
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
  have hrs := mapM_valueRegC hctx.toCallCtx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_genC _ _ _ (fun x => valClassOf ctx x) hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  exact ⟨intOut_outRegs _ _, trivial⟩

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2529` (`call_indirect`, `blr` of the callee): the results are the int vregs of
`gen_call_output` (`instData` admits an integer signature only, `sigIntB`). -/
theorem out_2529T {p : Program} (hp : Data p) (hpI : IndData p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInvT f ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2529 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2529.rhs env').run s1 =
      .ok (some out, (st', tr'))) : IntOut out ∧ CallInst inst := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
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
  have hrc := sigRets_classes_int (sigIntB_iff.mp (instData_callIndirect_int hd hs)).2
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
  have hrs := mapM_valueRegC hctx.toCallCtx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg _ _ ‹ctx.valueReg? callee = some _›
  subst htgt
  simp only [ctor_gen_call_args_genC _ _ _ (fun x => valClassOf ctx x) hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  exact ⟨intOut_outRegs _ _, trivial⟩

/-- **The `call` rules of `lower` give int-vreg results** in a float-capable context
with integer externs (rules 1031, 1032, 1033). -/
theorem out_callT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) (hx : f.externs.all (Compile.sigE ·.2.sig) = true) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst) {rl : Rule} (hrl : rl ∈ program.rulesOf TId.lower)
    (hid : rl.id = 1031 ∨ rl.id = 1032 ∨ rl.id = 1033) {cfg : Config}
    (hco : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule program (sem ctx) cfg m rl [.inst ii]).run (st, tr) = .ok (some env', s1))
    (heval : (evalExpr program (sem ctx) cfg n rl.rhs env').run s1 = .ok (some out, (st', tr'))) :
    IntOut out ∧ CallInst inst := by
  rcases hid with h | h | h
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2508 (by rw [h]; rfl)
    exact out_2508T data_program hctx hx hi hc hco hm hn hmatch heval
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2518 (by rw [h]; rfl)
    exact out_2518T data_program hctx hx hi hc hco hm hn hmatch heval
  · obtain rfl := eq_of_mem_of_id lower_ids_nodup hrl mem_lower_2529 (by rw [h]; rfl)
    exact out_2529T data_program indData_program hctx hx hi hc hco hm hn hmatch heval

end Backend.Proof.Cov
