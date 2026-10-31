import FV.Backend.Proof.IselTermFactsCallInd
import FV.Backend.Proof.IselTermFactsCallT

/-!
# Completeness of `lowerCheckT`: the outgoing area of `call_indirect` and `try_call_indirect`,
typed contexts

`IselTermFactsCallInd` over float-capable contexts (`CtxInvT`): the callee and the arguments of an
indirect call are in integer positions (`CtxInvT.intOps` for a `call_indirect`, `TermIntPos` for a
`try_call_indirect`), so their registers are integer vregs as in an integer context.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- `CallIndOutOk` over float-capable contexts. -/
def CallIndOutOkT (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInvT f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∀ sig callee args s, inst = .callIndirect sig callee args → f.sigDecls.lookup sig = some s →
      stackBytes s ≤ st'.outgoing

set_option maxHeartbeats 5000000 in
/-- **`call_indirect`** (`rule_lower_2529`), float-capable context. -/
theorem call_ind_outT {p : Program} (hp : Data p) (hpI : IndData p) :
    CallIndOutOkT p rule_lower_2529 := by
  intro f ctx hctx ii info inst hi hcl cfg hc m n st tr env' s1 out st' tr' hm hn hmatch heval
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
  have hai : ∀ x ∈ callee :: args, IntPos ctx x := fun x hx =>
    hctx.intOps ii info _ hi hcl x (by simpa [intArgs] using hx)
  have hrc := sigRets_classes_int (sigIntB_iff.mp (instData_callIndirect_int hd hs)).2
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
  have hrs := mapM_valueRegI (fun x r h hx => hctx.valueReg_int h hx)
    (fun x hx => hai x (List.mem_cons_of_mem _ hx)) ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg_int ‹ctx.valueReg? callee = some _› (hai callee List.mem_cons_self)
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
  intro sig0 callee0 args0 s0 hinst hs0
  injection hinst with h1 h2 h3
  subst h1 h2 h3
  rw [hs] at hs0
  cases hs0
  rw [hs2, hs1]
  simp [LState.emit, stackBytes, hl]
  omega

/-- **`lower` on a `call_indirect`**, float-capable context, raises the outgoing area to the
call-site signature's stack arguments. -/
theorem callIndOut_runTermT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat}
    {info : IInfo} {sig callee : Nat} {args : List Clif.ValueId} {s : Clif.Signature}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some (.callIndirect sig callee args))
    (hs : f.sigDecls.lookup sig = some s) {st : LState} {out : V} {st' : LState}
    {tr : List RuleId} (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    stackBytes s ≤ st'.outgoing := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, -, hmatch, heval⟩ := runTerm_lower_rule h
  obtain ⟨s', hs', hdat⟩ := instData_callIndirect_eq (hctx.data ii info _ hi hc)
  rw [hs] at hs'
  cases hs'
  have hok := List.all_eq_true.mp lower_callInd_fmts r hr
  simp only [callIndFmtOk] at hok
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
    have h54 : fT = 2454 := by omega
    rcases hid with ((h | h) | h)
    · exact absurd h54 h
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2529 (by rw [h]; rfl)] at hmatch heval
      exact call_ind_outT data_program indData_program f ctx hctx ii info _ hi hc {} rfl m n st #[]
        env' s1 out st' tr2 hm hn hmatch heval sig callee args s rfl hs
    · exact absurd hmatch (returnCallInd_unmatch hi hdat
        (eq_of_mem_of_id lower_ids_nodup hr mem_lower_2595 (by rw [h]; rfl)))
  · cases hok

/-- `TryIndOutOk` over contexts with `TryCtxOkT`, on a `try_call_indirect` whose callee and
arguments are in integer positions. -/
def TryIndOutOkT (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), TryCtxOkT f ctx →
  ∀ (ti : Nat) (callee : Nat) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (targets : List Label),
  (∀ x ∈ callee :: args, IntPos ctx x) →
  tryCallData f (.tryCallIndirect callee args et) = .ok data →
  ctx.insts[ti]? = some ⟨data, [], [], none⟩ →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    (matchRule p (sem ctx) cfg m r [.inst ti, .labels targets]).run (st, tr) =
      .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∀ s, f.sigDecls.lookup et.sig = some s → stackBytes s ≤ st'.outgoing

set_option maxHeartbeats 20000000 in
/-- **`try_call_indirect`** (`rule_lower_2561`), float-capable context. -/
theorem try_ind_outT {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) : TryIndOutOkT p rule_lower_2561 := by
  intro f ctx hcx ti callee args et data targets hai hd hi cfg hc m n st tr env' s1 out st' tr'
    hm hn hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig, items, he⟩ := tryCallIndData_spec hd
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
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegI hcx.valueReg (fun x hx => hai x (List.mem_cons_of_mem _ hx))
    ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hcx.valueReg _ _ ‹ctx.valueReg? callee = some _› (hai callee List.mem_cons_self)
  subst htgt
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Option.some.injEq] at *
  isel_destruct; subst_vars
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  intro s0 hs0
  rw [exnTableOpnd_sig he] at hs0
  cases hs0
  simp only at hs1 hs2
  rw [hs2, hs1]
  simp only [LState.emit, LState.fresh]
  simp [stackBytes, hl]
  try omega

/-- **`lower_branch` on a `try_call_indirect`**, float-capable context, raises the outgoing area
to the call-site signature's stack arguments. -/
theorem tryIndOut_runTermT {f : Clif.Function} {ctx : Ctx} (hcx : TryCtxOkT f ctx) {ti : Nat}
    {callee : Clif.ValueId} {args : List Clif.ValueId} {et : Clif.ExnTable} {s : Clif.Signature}
    {data : V} (hai : ∀ x ∈ callee :: args, IntPos ctx x)
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) (hs : f.sigDecls.lookup et.sig = some s)
    {targets : List Label} {st : LState} {out : V} {st' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower_branch" [.inst ti, .labels targets] st = .ok (some out, st', tr)) :
    stackBytes s ≤ st'.outgoing := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, -, hmatch, heval⟩ := runTerm_lower_branch_rule h
  cases hroot : tryIndRootRule r
  · exact absurd hmatch (tryInd_unmatch hr hroot hd hi)
  · simp only [tryIndRootRule, beq_iff_eq] at hroot
    rw [eq_of_mem_of_rid lower_branch_ids_nodup hr mem_lower_branch_2561 (by rw [hroot]; rfl)]
      at hmatch heval
    exact try_ind_outT data_program tryData_program indData_program tryIndData_program f ctx hcx
      ti callee args et data targets hai hd hi {} rfl m n st #[] env' s1 out st' tr2 hm hn hmatch
      heval s hs

end Backend.Proof
