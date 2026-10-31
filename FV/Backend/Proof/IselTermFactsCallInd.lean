import FV.Backend.Proof.IselTermFacts
import FV.Backend.Proof.IselCtlTryInd

/-!
# Completeness of `lowerCheck`: the outgoing area of `call_indirect` and `try_call_indirect`

The `call_indirect` rule (`rule_lower_2529`, id 1033) and the `try_call_indirect` rule
(`rule_lower_2561`, id 1036) raise the outgoing area to the call-site signature's stack-argument
size (`stackBytes`, S5), as the `call` and `try_call` rules do (`IselTermFactsCall`). The
symbolic executions are `call_ind_ruleOk`'s and `try_ind_ruleOk`'s; the only other rule of
`lower` with the `CallIndirect` format is `return_call_indirect`'s (`rule_lower_2595`, id 1040),
whose opcode never matches a `call_indirect`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

/-- A call-site signature of `f`'s indirect calls is a `call_indirect`'s or a
`try_call_indirect`'s. -/
theorem mem_indSigs {f : Clif.Function} {s : Clif.Signature} (h : s ∈ indSigs f) :
    ∃ B ∈ f.blocks, (∃ st ∈ B.body, ∃ sig c args, st.inst = .callIndirect sig c args ∧
      f.sigDecls.lookup sig = some s) ∨
      (∃ c args et, B.term = .tryCallIndirect c args et ∧ f.sigDecls.lookup et.sig = some s) := by
  unfold indSigs at h
  obtain ⟨B, hB, hs⟩ := List.mem_flatMap.mp h
  refine ⟨B, hB, ?_⟩
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨st, hst, he⟩ := List.mem_filterMap.mp hs
    left
    cases hi : st.inst with
    | callIndirect sig c args =>
      rw [hi] at he
      exact ⟨st, hst, sig, c, args, hi, he⟩
    | _ => simp [hi] at he
  · right
    cases ht : B.term with
    | tryCallIndirect c args et =>
      rw [ht] at hs
      exact ⟨c, args, et, rfl, by simpa using hs⟩
    | _ => simp [ht] at hs

set_option maxRecDepth 20000

/-! ## `call_indirect` -/

/-- The data of a `call_indirect` instruction. -/
theorem instData_callIndirect_eq {f : Clif.Function} {sig callee : Nat} {args : List Nat} {d : V}
    (h : instData f (.callIndirect sig callee args) = .ok d) :
    ∃ s, f.sigDecls.lookup sig = some s ∧
      d = .data 152 7 [.data 151 9 [], .values (callee :: args), .op (.sig s)] := by
  simp only [instData] at h
  split at h
  · rename_i s hs
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨s, hs, by rw [← h]; rfl⟩
    · cases h
  · cases h

/-- `IndRuleOk` with the outgoing-area conclusion. -/
def CallIndOutOk (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), CtxInv f ctx →
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
/-- **`call_indirect`** (`rule_lower_2529`). -/
theorem call_ind_out {p : Program} (hp : Data p) (hpI : IndData p) :
    CallIndOutOk p rule_lower_2529 := by
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
  intro sig0 callee0 args0 s0 hinst hs0
  injection hinst with h1 h2 h3
  subst h1 h2 h3
  rw [hs] at hs0
  cases hs0
  rw [hs2, hs1]
  simp [LState.emit, stackBytes, hl]
  omega

/-! ### The other rules on a `call_indirect` -/

/-- Every rule of `lower` with the `CallIndirect` format (2454) is the `call_indirect` rule (1033)
or the `return_call_indirect` rule (1040). -/
def callIndFmtOk (r : Rule) : Bool :=
  match ruleFmt r with
  | some fT => 2447 ≤ fT && fT < 2447 + 36 && (fT != 2454 || r.id == 1033 || r.id == 1040)
  | none => false

/-- `callIndFmtOk` holds for every rule of `lower` (decided over the exported rule data). -/
theorem lower_callInd_fmts : (program.rulesOf TId.lower).all callIndFmtOk = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-- `rule_lower_2595` (`return_call_indirect`) is a rule of `lower`. -/
theorem mem_lower_2595 : rule_lower_2595 ∈ program.rulesOf TId.lower :=
  List.mem_iff_getElem?.mpr ⟨348, by rw [show TId.lower = 686 from rfl, data_program.r686]; rfl⟩

/-- Term 2295 of the exported program is the opcode `ReturnCallIndirect`. -/
theorem program_term_2295 : Interp.termOf program 2295 = .ok T.«Opcode.ReturnCallIndirect» := rfl

/-- The `return_call_indirect` rule (opcode `ReturnCallIndirect`) never matches a
`call_indirect`. -/
theorem returnCallInd_unmatch {ctx : Ctx} {ii : Nat} {info : IInfo} {callee : Nat}
    {args : List Nat} {s : Clif.Signature} (hi : ctx.insts[ii]? = some info)
    (hdat : info.data = .data 152 7 [.data 151 9 [], .values (callee :: args), .op (.sig s)])
    {r : Rule} (hr : r = rule_lower_2595) {cfg : Config} {m : Nat}
    {s0 s1 : LState × Array RuleId} {env' : Interp.Env V} :
    (matchRule program (sem ctx) cfg m r [.inst ii]).run s0 ≠ .ok (some env', s1) := by
  intro hmatch
  cases m with
  | zero => rw [matchRule.eq_1] at hmatch; cases hmatch
  | succ m =>
    obtain ⟨env0, ha, -⟩ := matchRule_some_inv hmatch
    subst hr
    obtain ⟨e1, h1, -⟩ := matchArgs_cons_inv ha
    obtain ⟨fs, hx, hm⟩ := matchPat_extract_inv data_program.t209 term_209_kind rfl h1
    rw [sem_extract] at hx
    obtain ⟨info', hi', rfl⟩ := ext_inst_data_value_inv hx
    rw [hi] at hi'
    cases hi'
    obtain ⟨e2, -, hm2⟩ := matchArgs_cons_inv hm
    obtain ⟨e3, hp3, -⟩ := matchArgs_cons_inv hm2
    obtain ⟨fs', hu, hargs⟩ := matchPat_enum_inv program_term_2454 term_2454_kind hp3
    have hfs := sem_unData_inv hu
    rw [hdat] at hfs
    simp only [V.data.injEq, true_and] at hfs
    subst hfs
    obtain ⟨e4, hp4, -⟩ := matchArgs_cons_inv hargs
    obtain ⟨fs2, hu2, -⟩ := matchPat_enum_inv program_term_2295 rfl hp4
    have h8 := sem_unData_inv hu2
    simp at h8

/-- **`lower` on a `call_indirect`** raises the outgoing area to the call-site signature's
stack arguments. -/
theorem callIndOut_runTerm {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
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
      exact call_ind_out data_program indData_program f ctx hctx ii info _ hi hc {} rfl m n st #[]
        env' s1 out st' tr2 hm hn hmatch heval sig callee args s rfl hs
    · exact absurd hmatch (returnCallInd_unmatch hi hdat
        (eq_of_mem_of_id lower_ids_nodup hr mem_lower_2595 (by rw [h]; rfl)))
  · cases hok

/-! ## `try_call_indirect` -/

/-- `TryIndRuleOk` with the outgoing-area conclusion, in a context with `buildCtx`'s function and
value registers (`tryCtx`'s). -/
def TryIndOutOk (p : Program) (r : Rule) : Prop :=
  ∀ (f : Clif.Function) (ctx : Ctx), TryCtxOk f ctx →
  ∀ (ti : Nat) (callee : Nat) (args : List Nat) (et : Clif.ExnTable) (data : V)
    (targets : List Label),
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
/-- **`try_call_indirect`** (`rule_lower_2561`). -/
theorem try_ind_out {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) : TryIndOutOk p rule_lower_2561 := by
  intro f ctx hcx ti callee args et data targets hd hi cfg hc m n st tr env' s1 out st' tr' hm hn
    hmatch heval
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
  have hrs := mapM_valueReg' hcx.valueReg ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hcx.valueReg _ _ ‹ctx.valueReg? callee = some _›
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

/-- No rule of `lower_branch` other than 1036 matches a `try_call_indirect` (`tryIndUnmatchable`,
without `CtxInv`). -/
theorem tryInd_unmatch {r : Rule} (hr : r ∈ program.rulesOf TId.lower_branch)
    (hroot : tryIndRootRule r = false) {f : Clif.Function} {ctx : Ctx} {ti : Nat} {callee : Nat}
    {args : List Nat} {et : Clif.ExnTable} {data : V} {targets : List Label}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (hi : ctx.insts[ti]? = some ⟨data, [], [], none⟩) {cfg : Config} {m : Nat}
    {s : LState × Array RuleId} {env' : Interp.Env V} {s1 : LState × Array RuleId} :
    (matchRule program (sem ctx) cfg m r [.inst ti, .labels targets]).run s ≠
      .ok (some env', s1) := by
  intro hmatch
  have hok := List.all_eq_true.mp lower_branch_tryInd_fmts r hr
  simp only [tryIndFmtOk, hroot, Bool.false_or] at hok
  split at hok
  · rename_i fT hfT
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
    obtain ⟨⟨hlo, hhi⟩, h1⟩ := hok
    obtain ⟨info, fs, hinfo, hdat⟩ :=
      ruleFmt_match (vs := [.labels targets]) data_program fmtKinds_program hfT hlo hhi hmatch
    rw [hi] at hinfo
    cases hinfo
    obtain ⟨sig, items, he⟩ := tryCallIndData_spec hd
    rw [tryCallIndData_eq he] at hd
    cases hd
    simp only [V.data.injEq] at hdat
    omega
  · cases hok

/-- **`lower_branch` on a `try_call_indirect`** raises the outgoing area to the call-site
signature's stack arguments. -/
theorem tryIndOut_runTerm {f : Clif.Function} {ctx : Ctx} (hcx : TryCtxOk f ctx) {ti : Nat}
    {callee : Clif.ValueId} {args : List Clif.ValueId} {et : Clif.ExnTable} {s : Clif.Signature}
    {data : V} (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
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
    exact try_ind_out data_program tryData_program indData_program tryIndData_program f ctx hcx ti
      callee args et data targets hd hi {} rfl m n st #[] env' s1 out st' tr2 hm hn hmatch heval s hs

end Backend.Proof

namespace Backend.Proof.Driver

open Backend Backend.Proof

/-- Lowering a `call_indirect` raises the outgoing area to the call-site signature's stack
arguments. -/
theorem callInd_outgoing {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ii : Nat}
    {info : IInfo} {sig callee : Nat} {args : List Clif.ValueId} {s : Clif.Signature}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some (.callIndirect sig callee args))
    (hs : f.sigDecls.lookup sig = some s) {st : LState} {out : V} {st' : LState}
    {tr : List Isle.RuleId} (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    stackBytes s ≤ st'.outgoing :=
  callIndOut_runTerm hctx hi hc hs h

/-- Lowering a `try_call_indirect` raises the outgoing area to the call-site signature's stack
arguments. -/
theorem tryInd_outgoing {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hti : ti < ctx.insts.size) {callee : Clif.ValueId} {args : List Clif.ValueId}
    {et : Clif.ExnTable} {s : Clif.Signature} {data : V}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (hs : f.sigDecls.lookup et.sig = some s) {trs : List Reg × List Reg} {targets : List Label}
    {st : LState} {out : V} {st' : LState} {tr : List Isle.RuleId}
    (h : tryCallF ctx ti data trs targets st = .ok (some out, st', tr)) :
    stackBytes s ≤ st'.outgoing := by
  have hlt : ctx.insts[ti]? = some ctx.insts[ti] := Array.getElem?_eq_getElem hti
  exact tryIndOut_runTerm (ctx := tryCtx ctx ti data trs) ⟨hctx.func, hctx.valueReg⟩ hd
    (termCtx_insts_self hlt data) hs h

end Backend.Proof.Driver
