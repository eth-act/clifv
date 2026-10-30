import FV.Backend.Proof.SpillLocal
import FV.Backend.Proof.RegallocTac
import FV.Backend.Proof.IselCtlUnmatch
import FV.Backend.Proof.IselExcl
import FV.Backend.Proof.IselCtl
import FV.Backend.Proof.IselCtlTryInd
import FV.Backend.Proof.VCodeSemICall

/-!
# One VCode call per CLIF call: the call counts of the ISLE lowering (SEM1, `docs/plans/uninit.md` §5.9)

The counted CLIF → VCode simulation (`E2E.IselSimI`) needs two properties of the ISLE lowering:
a `call`/`call_indirect` statement lowers to code with exactly one VCode call
(`MInst.isCallI`), and a `try_call`/`try_call_indirect`'s code has one call, its last
instruction. Both follow from the rule data:

* **Rule-table certificate** (`lower_call_fmts`, one kernel decision over the exported rules of
  `lower`): every root rule of `lower` is a call root (rule ids 1031–1033), outside the closure
  (`ExcludedUnmatchable`), or names an `InstructionData` format other than `Call`/`CallIndirect`
  at the root of its pattern (`ruleFmt`), so it never matches a call (`ruleFmt_match`). For
  `lower_branch`: `TryUnmatchable`/`TryIndUnmatchable` (only 1034/1035, resp. 1036, match).
* **The call roots' runs** (`callRun_2508`/`_2518`/`_2529`, `tryRun_2542`/`_2551`/`_2561`: the
  inversions of `IselShpCall`'s `run_*` and `IselShpTry`'s `shpTry_*`, concluding the call count
  instead of the shapes): stack-argument stores, possibly a GOT load, and one call.

`CallsSince k s0 s`: the instructions emitted from `s0` to `s` contain `k` calls.
Results: **`lower_callsOne`** (a statement's `lower`), **`tryCall_callsOne`**,
**`tryCallInd_callsOne`** (a `try_call`'s `lower_branch` in its `try_call` context).
-/

namespace Backend.Proof.Cov

open Backend Backend.Proof Backend.Proof.Spill Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## The call count of a lowering run -/

/-- The instructions emitted from `s0` to `s` contain exactly `k` VCode calls. -/
def CallsSince (k : Nat) (s0 s : LState) : Prop :=
  ∃ ms : List MInst, s.emitted = s0.emitted ++ ms.toArray ∧ callsI ms = k

theorem callsI_argStores (E : List (Nat × Nat × Nat)) : callsI (E.map argStore) = 0 := by
  unfold callsI
  rw [List.countP_eq_zero]
  intro m hm
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
  simp [argStore, MInst.isCallI]

theorem callsSince_stores {st s : LState} (E : List (Nat × Nat × Nat))
    (h : s.emitted = st.emitted ++ (E.map argStore).toArray) : CallsSince 0 st s :=
  ⟨_, h, callsI_argStores E⟩

theorem callsSince_emit {k : Nat} {st s s' : LState} {c : MInst} (h : CallsSince k st s)
    (he : s' = s.emit c) : CallsSince (k + if c.isCallI then 1 else 0) st s' := by
  obtain ⟨ms, hms, hk⟩ := h
  refine ⟨ms ++ [c], by rw [he]; simp [LState.emit, hms], ?_⟩
  unfold callsI at hk ⊢
  rw [List.countP_append, hk]
  cases hc : c.isCallI <;> simp [hc]

theorem callsSince_congr {k : Nat} {st s s' : LState} (h : CallsSince k st s)
    (he : s'.emitted = s.emitted) : CallsSince k st s' := by
  obtain ⟨ms, hms, hk⟩ := h
  exact ⟨ms, he.trans hms, hk⟩

/-- Stack-argument stores followed by one call have one call. -/
theorem callsI_stores_call (E : List (Nat × Nat × Nat)) (ci : CallInfo) :
    callsI (E.map argStore ++ [.call ci]) = 1 := by
  unfold callsI
  rw [List.countP_append]
  have := callsI_argStores E
  unfold callsI at this
  rw [this]
  simp [MInst.isCallI]

/-- Stack-argument stores, a GOT load and one call have one call. -/
theorem callsI_stores_got_call (E : List (Nat × Nat × Nat)) (r : Reg) (nm : String)
    (ci : CallInfo) : callsI (E.map argStore ++ [.loadExtNameGot r nm, .call ci]) = 1 := by
  unfold callsI
  rw [List.countP_append]
  have := callsI_argStores E
  unfold callsI at this
  rw [this]
  simp [MInst.isCallI]

/-! ## The `call` root rules of `lower` (1031, 1032, 1033) -/

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2508` (`bl`, 1031) emits one call (`run_2508`'s inversion). -/
theorem callRun_2508 {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2508 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2508.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CallsSince 1 st st' := by
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
  have hrc := hctx.call_retClasses hi hcl hext
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
  exact callsSince_emit (callsSince_stores (stackEnts ((locs.zip args).zip bytes))
    (by rw [hs1]; simp [freshN_emitted])) hs2

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2518` (GOT + `blr`, 1032) emits one call (`run_2518`'s inversion). -/
theorem callRun_2518 {p : Program} (hp : Data p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2518 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2518.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CallsSince 1 st st' := by
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
  have hrc := hctx.call_retClasses hi hcl hext
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
  exact callsSince_emit (callsSince_congr (callsSince_emit (callsSince_stores
    (stackEnts ((locs.zip args).zip bytes)) (by simp [LState.fresh, freshN_emitted])) hs0)
    (by rw [hs1])) hs2

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2529` (`blr` of the callee value, 1033) emits one call (`run_2529`'s inversion). -/
theorem callRun_2529 {p : Program} (hp : Data p) (hpI : IndData p) {f : Clif.Function} {ctx : Ctx}
    (hctx : CtxInv f ctx) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hcl : info.clif = some inst) {cfg : Config}
    (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState} {tr : Array RuleId}
    {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V} {st' : LState}
    {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem ctx) cfg m rule_lower_2529 [.inst ii]).run (st, tr) =
      .ok (some env', s1))
    (heval : (evalExpr p (sem ctx) cfg n rule_lower_2529.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CallsSince 1 st st' := by
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
  exact callsSince_emit (callsSince_stores (stackEnts ((locs.zip args).zip bytes))
    (by rw [hs1]; simp [freshN_emitted])) hs2

/-! ## The rule-table certificate for `lower` -/

/-- A root rule of `lower` is a call root (1031–1033), outside the closure, or names a root
format whose `InstructionData` variant is neither `Call` nor `CallIndirect`. -/
def callFmtOk (r : Rule) : Bool :=
  callRootRule r || indRootRule r || !closureRoot r ||
    match ruleFmt r with
    | some fT => 2447 ≤ fT && fT < 2447 + 36 &&
        (variantNames 152)[fT - 2447]? != some "Call" &&
        (variantNames 152)[fT - 2447]? != some "CallIndirect"
    | none => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **The certificate** (one kernel decision over the exported rules of `lower`). -/
theorem lower_call_fmts : (program.rulesOf TId.lower).all callFmtOk = true := by
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

/-- The data of a `call`/`call_indirect` has format variant `Call`/`CallIndirect`. -/
theorem instData_call_fmt {f : Clif.Function} {inst : Clif.Inst} {k : Nat} {fs : List V}
    (hcl : (∃ fn args, inst = .call fn args) ∨ ∃ sig callee args, inst = .callIndirect sig callee args)
    (h : instData f inst = .ok (.data 152 k fs)) :
    (variantNames 152)[k]? = some "Call" ∨ (variantNames 152)[k]? = some "CallIndirect" := by
  rcases hcl with ⟨fn, args, rfl⟩ | ⟨sig, callee, args, rfl⟩
  · simp only [instData] at h
    split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, instDataV] at h
        obtain ⟨h1, -, -⟩ := mkVariant_eq_data h
        rw [show tyInstData = 152 from rfl] at h1
        exact .inl h1
      · cases h
    · cases h
  · simp only [instData] at h
    split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, instDataV] at h
        obtain ⟨h1, -, -⟩ := mkVariant_eq_data h
        rw [show tyInstData = 152 from rfl] at h1
        exact .inr h1
      · cases h
    · cases h

set_option maxRecDepth 20000 in
/-- **A `call`/`call_indirect` statement's `lower` run emits exactly one VCode call** (the
applied form, any fuel). -/
theorem lower_callsOne_apply {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hE : Compile.functionE f = true) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hcl : (∃ fn args, inst = .call fn args) ∨ ∃ sig callee args, inst = .callIndirect sig callee args)
    {cfg : Config} (hco : cfg.checkOverlap = false) {n : Nat}
    (hn : 1002 + (program.rulesOf TId.lower).length ≤ n) {ty : TypeId} {st : LState}
    {tr : Array RuleId} {out : V} {st' : LState} {tr' : Array RuleId}
    (h : (applyTerm program (sem ctx) cfg (n + 1) ty TId.lower [.inst ii]).run (st, tr) =
      .ok (some out, (st', tr'))) :
    CallsSince 1 st st' := by
  change 1002 + (program.rulesOf 686).length ≤ n at hn
  obtain ⟨r, pre0, post0, hsplit, -, m, env', s1, st2, tr2, hmn, hmatch, heval, hs⟩ :=
    applyTerm_internal_some_first hco data_program.t686 term_686_kind rfl h
  have hr : r ∈ program.rulesOf TId.lower := by
    change r ∈ program.rulesOf 686; rw [hsplit]; simp
  simp only [Prod.mk.injEq] at hs
  obtain ⟨rfl, -⟩ := hs
  cases hroot : closureRoot r
  · exact absurd hmatch
      (excludedUnmatchable r hr hroot f ctx hctx hE ii info inst hi hc cfg m (st, tr) env' s1)
  have hok := List.all_eq_true.mp lower_call_fmts r hr
  by_cases hid : r.id = 1031 ∨ r.id = 1032 ∨ r.id = 1033
  · rcases hid with hid | hid | hid
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2508 (by rw [hid]; rfl)] at hmatch heval
      exact callRun_2508 data_program hctx hi hc hco (by omega) (by omega) hmatch heval
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2518 (by rw [hid]; rfl)] at hmatch heval
      exact callRun_2518 data_program hctx hi hc hco (by omega) (by omega) hmatch heval
    · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2529 (by rw [hid]; rfl)] at hmatch heval
      exact callRun_2529 data_program indData_program hctx hi hc hco (by omega) (by omega)
        hmatch heval
  · exfalso
    have hcr : callRootRule r = false := by
      unfold callRootRule
      rw [Bool.or_eq_false_iff]
      exact ⟨beq_eq_false_iff_ne.mpr fun h => hid (.inl h),
        beq_eq_false_iff_ne.mpr fun h => hid (.inr (.inl h))⟩
    have hir : indRootRule r = false := by
      unfold indRootRule
      exact beq_eq_false_iff_ne.mpr fun h => hid (.inr (.inr h))
    simp only [callFmtOk, hcr, hir, hroot, Bool.not_true, Bool.false_or] at hok
    split at hok
    · rename_i fT hfT
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hok
      obtain ⟨⟨⟨hlo, hhi⟩, h1⟩, h2⟩ := hok
      obtain ⟨info', fs, hinfo, hdat⟩ :=
        ruleFmt_match (vs := []) data_program fmtKinds_program hfT hlo hhi hmatch
      rw [hi] at hinfo
      cases hinfo
      have hd := hctx.data ii _ inst hi hc
      rw [hdat] at hd
      rcases instData_call_fmt hcl hd with h3 | h3
      · exact h1 h3
      · exact h2 h3
    · cases hok

set_option maxRecDepth 20000 in
/-- **A `call`/`call_indirect` statement's `lower` emits exactly one VCode call** (the
backend's call `runTerm ctx "lower" [.inst ii]`, as `lowerFunction` makes it). -/
theorem lower_callsOne {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    (hE : Compile.functionE f = true) {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some inst)
    (hcl : (∃ fn args, inst = .call fn args) ∨ ∃ sig callee args, inst = .callIndirect sig callee args)
    {st : LState} {out : V} {st' : LState} {tr : List RuleId}
    (h : runTerm ctx "lower" [.inst ii] st = .ok (some out, st', tr)) :
    CallsSince 1 st st' := by
  unfold runTerm Interp.run at h
  rw [program_termByName_lower] at h
  dsimp only at h
  cases ha : (applyTerm program (sem ctx) {} 1000000 T.lower.ret T.lower.id [.inst ii]).run
      (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf TId.lower).length ≤ 1000 := by
      rw [show TId.lower = 686 from rfl, data_program.r686]; decide
    exact lower_callsOne_apply hctx hE hi hc hcl rfl (by omega) ha

/-! ## The `try_call` root rules of `lower_branch` (1034, 1035, 1036) -/

set_option maxHeartbeats 5000000 in
/-- `rule_lower_2542` (`bl`, id 1034) on a `try_call` emits one call (`shpTry_bl`'s inversion). -/
theorem tryRun_2542 {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInv f c)
    {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState}
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩)
    (htr : tryRegsOf sig lo = some (c.tryRegs, st1)) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2542 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2542.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CallsSince 1 st st' := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
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
  have hrs := mapM_valueReg hctx ‹List.mapM c.valueReg? args = some _›
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
  simp only at hs1 hs2
  exact callsSince_emit (callsSince_stores (stackEnts ((locs.zip args).zip bytes))
    (by rw [hs1] <;> simp [freshN_emitted])) hs2

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2551` (GOT + `blr`, id 1035) on a `try_call` emits one call (`shpTry_got`'s
inversion). -/
theorem tryRun_2551 {p : Program} (hp : Data p) (hpT : TryData p) {f : Clif.Function} {c : Ctx}
    (hctx : CtxInv f c)
    {ti : Nat} {fn : Clif.FnRef} {args : List Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState}
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩)
    (htr : tryRegsOf sig lo = some (c.tryRegs, st1)) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2551 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2551.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CallsSince 1 st st' := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := c) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := c) hc
    (n := n) (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := c) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
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
  have hrs := mapM_valueReg hctx ‹List.mapM c.valueReg? args = some _›
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
  simp only at hs0 hs1 hs2
  exact callsSince_emit (callsSince_congr (callsSince_emit (callsSince_stores
    (stackEnts ((locs.zip args).zip bytes)) (by simp [LState.fresh, freshN_emitted])) hs0)
    (by rw [hs1])) hs2

set_option maxHeartbeats 20000000 in
/-- `rule_lower_2561` (`blr` of the callee value, id 1036) on a `try_call_indirect` emits one
call (`shpTry_ind`'s inversion). -/
theorem tryRun_2561 {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) {f : Clif.Function} {c : Ctx} (hctx : CtxInv f c)
    {ti : Nat} {callee : Nat} {args : List Nat} {et : Clif.ExnTable} {data : V}
    {sig : Clif.Signature} {items : List (Option Nat)} {lo st1 : LState}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items))
    (hi : c.insts[ti]? = some ⟨data, [], [], none⟩)
    (htr : tryRegsOf sig lo = some (c.tryRegs, st1)) {targets : List Label}
    {cfg : Config} (hc : cfg.checkOverlap = false) {m n : Nat} {st : LState}
    {tr : Array RuleId} {env' : Isle.Interp.Env V} {s1 : LState × Array RuleId} {out : V}
    {st' : LState} {tr' : Array RuleId} (hm : 1000 ≤ m) (hn : 1000 ≤ n)
    (hmatch : (matchRule p (sem c) cfg m rule_lower_2561 [.inst ti, .labels targets]).run
      (st, tr) = .ok (some env', s1))
    (heval : (evalExpr p (sem c) cfg n rule_lower_2561.rhs env').run s1 =
      .ok (some out, (st', tr'))) :
    CallsSince 1 st st' := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
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
  have hrs := mapM_valueReg hctx ‹List.mapM c.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg _ _ ‹c.valueReg? callee = some _›
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
  simp only at hs1 hs2
  exact callsSince_emit (callsSince_stores (stackEnts ((locs.zip args).zip bytes))
    (by rw [hs1] <;> simp)) hs2

/-! ## `lower_branch` on a `try_call` -/

set_option maxRecDepth 20000 in
/-- **A `try_call`'s `lower_branch` (in its `try_call` context) emits exactly one VCode call.**
Only the root rules 1034, 1035 match a `try_call` (`tryUnmatchable`). -/
theorem tryCall_callsOne {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {fn : Clif.FnRef} {args : List Nat}
    {et : Clif.ExnTable} {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    {lo st1 : LState} {trs : List Reg × List Reg}
    (hd : tryCallData f (.tryCall fn args et) = .ok data) (he : exnTableOpnd f et = .ok (sig, items))
    (htr : tryRegsOf sig lo = some (trs, st1)) {targets : List Label} {st : LState}
    {out : V} {st' : LState} {tr : List RuleId}
    (h : runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets] st =
      .ok (some out, st', tr)) :
    CallsSince 1 st st' := by
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { ctxInv_termCtx hctx hph data with }
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
  generalize tryCtx ctx ti data trs = c at hctx' hi htr' h
  unfold runTerm Interp.run at h
  rw [program_termByName_lower_branch] at h
  dsimp only at h
  cases ha : (applyTerm program (sem c) {} 1000000 T.lower_branch.ret T.lower_branch.id
      [.inst ti, .labels targets]).run (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf 687).length ≤ 1000 := by
      rw [data_program.r687]; decide
    change (applyTerm program (sem c) {} (999999 + 1) T.lower_branch.ret 687
      [.inst ti, .labels targets]).run (st, #[]) = _ at ha
    obtain ⟨r, pre0, post0, hsplit, -, m, env', s1, st3, tr3, hmn, hmatch, heval, hs⟩ :=
      applyTerm_internal_some_first rfl data_program.t687 term_687_kind rfl ha
    have hr : r ∈ program.rulesOf TId.lower_branch := by
      change r ∈ program.rulesOf 687; rw [hsplit]; simp
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
      rw [show TId.lower_branch = 687 from rfl, data_program.r687]
      decide +kernel
    cases hroot : tryRootRule r
    · exact absurd hmatch (tryUnmatchable r hr hroot f c hctx' ti fn args et data targets hd hi
        {} m (st, #[]) env' s1)
    · simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
      rcases hroot with hid | hid
      · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2542 (by rw [hid]; rfl)] at hmatch heval
        exact tryRun_2542 data_program tryData_program hctx' hd he hi htr' rfl (by omega) (by omega)
          hmatch heval
      · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2551 (by rw [hid]; rfl)] at hmatch heval
        exact tryRun_2551 data_program tryData_program hctx' hd he hi htr' rfl (by omega) (by omega)
          hmatch heval

set_option maxRecDepth 20000 in
/-- **A `try_call_indirect`'s `lower_branch` (in its `try_call` context) emits exactly one VCode
call.** Only the root rule 1036 matches a `try_call_indirect` (`tryIndUnmatchable`). -/
theorem tryCallInd_callsOne {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {ti : Nat}
    (hph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩) {callee : Nat} {args : List Nat}
    {et : Clif.ExnTable} {data : V} {sig : Clif.Signature} {items : List (Option Nat)}
    {lo st1 : LState} {trs : List Reg × List Reg}
    (hd : tryCallData f (.tryCallIndirect callee args et) = .ok data)
    (he : exnTableOpnd f et = .ok (sig, items))
    (htr : tryRegsOf sig lo = some (trs, st1)) {targets : List Label} {st : LState}
    {out : V} {st' : LState} {tr : List RuleId}
    (h : runTerm (tryCtx ctx ti data trs) "lower_branch" [.inst ti, .labels targets] st =
      .ok (some out, st', tr)) :
    CallsSince 1 st st' := by
  have hctx' : CtxInv f (tryCtx ctx ti data trs) := { ctxInv_termCtx hctx hph data with }
  have hi : (tryCtx ctx ti data trs).insts[ti]? = some ⟨data, [], [], none⟩ :=
    termCtx_insts_self hph data
  have htr' : tryRegsOf sig lo = some ((tryCtx ctx ti data trs).tryRegs, st1) := htr
  generalize tryCtx ctx ti data trs = c at hctx' hi htr' h
  unfold runTerm Interp.run at h
  rw [program_termByName_lower_branch] at h
  dsimp only at h
  cases ha : (applyTerm program (sem c) {} 1000000 T.lower_branch.ret T.lower_branch.id
      [.inst ti, .labels targets]).run (st, #[]) with
  | error e => rw [ha] at h; cases h
  | ok q =>
    obtain ⟨v, st2, tr2⟩ := q
    rw [ha] at h
    simp only [bind, Except.bind, pure, Except.pure] at h
    injection h with h
    injection h with h1 h2
    subst h1
    injection h2 with h2 _
    subst h2
    have hlen : (program.rulesOf 687).length ≤ 1000 := by
      rw [data_program.r687]; decide
    change (applyTerm program (sem c) {} (999999 + 1) T.lower_branch.ret 687
      [.inst ti, .labels targets]).run (st, #[]) = _ at ha
    obtain ⟨r, pre0, post0, hsplit, -, m, env', s1, st3, tr3, hmn, hmatch, heval, hs⟩ :=
      applyTerm_internal_some_first rfl data_program.t687 term_687_kind rfl ha
    have hr : r ∈ program.rulesOf TId.lower_branch := by
      change r ∈ program.rulesOf 687; rw [hsplit]; simp
    simp only [Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
      rw [show TId.lower_branch = 687 from rfl, data_program.r687]
      decide +kernel
    cases hroot : tryIndRootRule r
    · exact absurd hmatch (tryIndUnmatchable r hr hroot f c hctx' ti callee args et data targets
        hd hi {} m (st, #[]) env' s1)
    · simp only [tryIndRootRule, beq_iff_eq] at hroot
      rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2561 (by rw [hroot]; rfl)] at hmatch heval
      exact tryRun_2561 data_program tryData_program indData_program tryIndData_program hctx' hd he
        hi htr' rfl (by omega) (by omega) hmatch heval

end Backend.Proof.Cov
