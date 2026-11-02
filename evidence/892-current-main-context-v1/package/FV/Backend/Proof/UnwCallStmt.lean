import FV.Backend.Proof.IselCtlCallInd
import FV.Backend.Proof.IselTermFactsCall

/-!
# A call statement's code contains a call (S10g, #404)

`stmtCall_hasCall`: the driver's `lower` run on a `call` or `call_indirect` statement emits a
`call` (`UnwShape.calls`, where a raising callee ends the activation). The run commits to a rule
whose root format is the instruction's: for `Call` the `call` rules 1031 (`bl`), 1032 (GOT +
`blr`) and the `return_call` rules 1038, 1039, for `CallIndirect` the `call_indirect` rule 1033 and
the `return_call_indirect` rule 1040 (`lower_callHas_fmts`, one kernel decision over the exported
rules; the other formats never match, `ruleFmt_match`). The `return_call` rules never match a
call (their opcode differs, `returnCall_unmatch`, `returnCallInd_unmatch`) and each `call` rule
emits a call (`call_bl_has`, `call_got_has`, `call_ind_has`: the symbolic executions of
`IselTermFactsCall`/`IselShpCall` up to the emitted call).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-- A `lower` rule on a call statement emits a call. -/
def CallHasOk (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
  ∀ (ii : Nat) (info : IInfo) (inst : Clif.Inst), ctx.insts[ii]? = some info →
    info.clif = some inst →
  ∀ (cfg : Config), cfg.checkOverlap = false →
  ∀ (m n : Nat) (st : LState) (tr : Array RuleId) (env' : Interp.Env V) (s1 : LState × Array RuleId)
    (out : V) (st' : LState) (tr' : Array RuleId), 1000 ≤ m → 1000 ≤ n →
    (matchRule p (sem ctx) cfg m r [.inst ii]).run (st, tr) = .ok (some env', s1) →
    (evalExpr p (sem ctx) cfg n r.rhs env').run s1 = .ok (some out, (st', tr')) →
    ∃ ci, MInst.call ci ∈ st'.emitted.toList

theorem call_mem_emit (s : LState) (ci : CallInfo) :
    MInst.call ci ∈ (s.emit (.call ci)).emitted.toList := by
  simp [LState.emit]

set_option maxHeartbeats 5000000 in
/-- **`call`, colocated callee** (`rule_lower_2508`). -/
theorem call_bl_has {p : Program} (hp : Data p) : CallHasOk p rule_lower_2508 := by
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
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  have hrc := hctx.call_retClasses hi hcl hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2508] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_iff _ _ hrc, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, retRegsC_outRegs,
    outRegs_length,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, retRegsC_outRegs, outRegs_single, outRegs_length,
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
  rw [hs2]
  exact ⟨_, call_mem_emit _ _⟩

set_option maxHeartbeats 5000000 in
/-- **`call` through the GOT** (`rule_lower_2518`). -/
theorem call_got_has {p : Program} (hp : Data p) : CallHasOk p rule_lower_2518 := by
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
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  have hrc := hctx.call_retClasses hi hcl hext
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
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, retRegsC_outRegs, outRegs_single, outRegs_length,
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
    ite_true,
    ite_false, Option.some.injEq] at *
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
  rw [hs2]
  exact ⟨_, call_mem_emit _ _⟩

set_option maxHeartbeats 5000000 in
/-- **`call_indirect`** (`rule_lower_2529`, `blr` of the callee). -/
theorem call_ind_has {p : Program} (hp : Data p) (hpI : IndData p) : CallHasOk p rule_lower_2529 := by
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
  rw [hs2]
  exact ⟨_, call_mem_emit _ _⟩

/-! ## The other rules on a call statement -/

/-- The root format of every rule of `lower` is an `InstructionData` format; only the `call`
rules (1031, 1032) and the `return_call` rules (1038, 1039) name `Call` (2453), only the
`call_indirect` rule (1033) and the `return_call_indirect` rule (1040) name `CallIndirect`
(2454). -/
def callHasFmtOk (r : Rule) : Bool :=
  match ruleFmt r with
  | some fT => 2447 ≤ fT && fT < 2447 + 36 &&
      (fT != 2453 || r.id == 1031 || r.id == 1032 || r.id == 1038 || r.id == 1039) &&
      (fT != 2454 || r.id == 1033 || r.id == 1040)
  | none => false

/-- `callHasFmtOk` holds for every rule of `lower` (decided over the exported rule data). -/
theorem lower_callHas_fmts : (program.rulesOf TId.lower).all callHasFmtOk = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-- `rule_lower_2595` (`return_call_indirect`) is a rule of `lower`. -/
theorem mem_lower_2595 : rule_lower_2595 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨348, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

/-- Term 2295 of the exported program is the opcode `ReturnCallIndirect`. -/
theorem program_term_2295 : Interp.termOf program 2295 = .ok T.«Opcode.ReturnCallIndirect» := rfl

/-- The data of a `call_indirect` instruction. -/
theorem instData_callIndirect_eq {f : Clif.Function} {sig callee : Nat} {args : List Clif.ValueId}
    {d : V} (h : instData f (.callIndirect sig callee args) = .ok d) :
    ∃ s, d = .data 152 7 [.data 151 9 [], .values (callee :: args), .op (.sig s)] := by
  simp only [instData] at h
  split at h
  · rename_i s _
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨s, by rw [← h]; rfl⟩
    · cases h
  · cases h

/-- The `return_call_indirect` rule (opcode `ReturnCallIndirect`) never matches a
`call_indirect`. -/
theorem returnCallInd_unmatch {ctx : Ctx} {ii : Nat} {info : IInfo} {callee : Nat}
    {args : List Clif.ValueId} {s : Clif.Signature} (hi : ctx.insts[ii]? = some info)
    (hdat : info.data = .data 152 7 [.data 151 9 [], .values (callee :: args), .op (.sig s)])
    {cfg : Config} {m : Nat} {s0 s1 : LState × Array RuleId} {env' : Interp.Env V} :
    (matchRule program (sem ctx) cfg m rule_lower_2595 [.inst ii]).run s0 ≠ .ok (some env', s1) := by
  intro hmatch
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
    obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
    obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl h1
    rw [sem_extract] at hx
    obtain ⟨info', hi', rfl⟩ := ext_inst_data_value_inv hx
    rw [hi] at hi'
    cases hi'
    obtain ⟨e2, -, hm2⟩ := matchArgs_cons_inv hm
    obtain ⟨e3, hp3, -⟩ := matchArgs_cons_inv hm2
    obtain ⟨fs', hu, hargs⟩ := matchPat_enum_inv data_program.t2454 term_2454_kind hp3
    have hfs := sem_unData_inv hu
    rw [hdat] at hfs
    simp only [V.data.injEq, true_and] at hfs
    subst hfs
    obtain ⟨e4, hp4, -⟩ := matchArgs_cons_inv hargs
    obtain ⟨fs2, hu2, -⟩ := matchPat_enum_inv program_term_2295 rfl hp4
    have h9 := sem_unData_inv hu2
    simp at h9

/-! ## The driver's run -/

/-- **A call statement's lowering emits a call**: the driver's `lower` run on a `call` or
`call_indirect` statement that returns a value has emitted a `call`. -/
theorem stmtCall_hasCall {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {inst : Clif.Inst} (hi : ctx.insts[ii]? = some info)
    (hc : info.clif = some inst)
    (hcall : (∃ fn args, inst = .call fn args) ∨ ∃ sig callee args, inst = .callIndirect sig callee args)
    {s : LState} {out : V} {s' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower" [.inst ii] s = .ok (some out, s', tr)) :
    ∃ ci, MInst.call ci ∈ s'.emitted.toList := by
  obtain ⟨r, hr, m, n, env', s1, tr2, hm, hn, -, hmatch, heval⟩ := runTerm_lower_rule h
  have hok := List.all_eq_true.mp lower_callHas_fmts r hr
  simp only [callHasFmtOk] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
      beq_iff_eq] at hok
    obtain ⟨⟨⟨hlo, hhi⟩, hid⟩, hid'⟩ := hok
    obtain ⟨info', fs, hinfo, hd'⟩ :=
      ruleFmt_match (vs := []) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    rcases hcall with ⟨fn, args, rfl⟩ | ⟨sig, callee, args, rfl⟩
    · have hdat := instData_call_eq (hctx.data ii info _ hi hc)
      rw [hdat] at hd'
      simp only [V.data.injEq, true_and] at hd'
      have h53 : fT = 2453 := by omega
      rcases hid with ((((h | h) | h) | h) | h)
      · exact absurd h53 h
      · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2508 (by rw [h]; rfl)] at hmatch heval
        exact call_bl_has data_program f ctx hctx ii info _ hi hc {} rfl m n s #[] env' s1 out s' tr2
          hm hn hmatch heval
      · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2518 (by rw [h]; rfl)] at hmatch heval
        exact call_got_has data_program f ctx hctx ii info _ hi hc {} rfl m n s #[] env' s1 out s'
          tr2 hm hn hmatch heval
      · exact absurd hmatch (returnCall_unmatch hi hdat
          (.inl (eq_of_mem_of_id lower_ids_nodup hr mem_lower_2580 (by rw [h]; rfl))))
      · exact absurd hmatch (returnCall_unmatch hi hdat
          (.inr (eq_of_mem_of_id lower_ids_nodup hr mem_lower_2587 (by rw [h]; rfl))))
    · obtain ⟨sg, hdat⟩ := instData_callIndirect_eq (hctx.data ii info _ hi hc)
      rw [hdat] at hd'
      simp only [V.data.injEq, true_and] at hd'
      have h54 : fT = 2454 := by omega
      rcases hid' with ((h | h) | h)
      · exact absurd h54 h
      · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2529 (by rw [h]; rfl)] at hmatch heval
        exact call_ind_has data_program indData_program f ctx hctx ii info _ hi hc {} rfl m n s #[]
          env' s1 out s' tr2 hm hn hmatch heval
      · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2595 (by rw [h]; rfl)] at hmatch
        exact absurd hmatch (returnCallInd_unmatch hi hdat)
  · cases hok

end Backend.Proof
