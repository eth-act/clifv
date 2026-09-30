import FV.Backend.Proof.IselCtlCallRules

/-!
# Family Ctl: the `call_indirect` rule

`IndRuleOk` for `rule_lower_2529` (`blr` of the callee value's register, rule id 1033): as the
GOT call (`call_got_ruleOk`, rule 1032) with the callee value's vreg (`put_in_reg`) as the
target instead of a `loadExtNameGot`, and the call site's signature (`sigN`) as the ABI. The
CLIF outcome is the extern at the callee address (`Clif.callExternAt`); the contract
`IndCallsRefine` relates the `blr` of that address to it.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## ISLE data of the indirect-call rules

The terms the `call_indirect`/`try_call_indirect` rules reach beyond `Data`. -/

@[isel_data] theorem term_196_kind : T.«value_slice_unwrap».kind =
    (.decl ⟨false, false, false, false⟩ none (some (.external "value_slice_unwrap" false))) := rfl
@[isel_data] theorem term_196_name : T.«value_slice_unwrap».name = "value_slice_unwrap" := rfl
@[isel_data] theorem term_2293_kind : T.«Opcode.CallIndirect».kind = (.enumVariant 9) := rfl
@[isel_data] theorem term_2293_name : T.«Opcode.CallIndirect».name = "Opcode.CallIndirect" := rfl
@[isel_data] theorem term_2454_kind : T.«InstructionData.CallIndirect».kind = (.enumVariant 7) :=
  rfl
@[isel_data] theorem term_2454_name :
    T.«InstructionData.CallIndirect».name = "InstructionData.CallIndirect" := rfl

/-- The term facts of the indirect-call rules beyond `Data`. -/
structure IndData (p : Program) : Prop where
  t196 : Interp.termOf p 196 = pure T.«value_slice_unwrap»
  t2293 : Interp.termOf p 2293 = pure T.«Opcode.CallIndirect»
  t2454 : Interp.termOf p 2454 = pure T.«InstructionData.CallIndirect»

theorem indData_program : IndData program := ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 20000 in
theorem variantNames_CallIndirect_fmt : (variantNames 152)[7]? = some "CallIndirect" := rfl
set_option maxRecDepth 20000 in
theorem variantNames_CallIndirect_op : (variantNames 151)[9]? = some "CallIndirect" := rfl

/-- A matched `CallIndirect (CallIndirect) fs` is a `call_indirect` with a declared signature. -/
theorem instData_callIndirect_inv {f : Clif.Function} {cl : Clif.Inst} {fs : List V}
    (h : instData f cl = .ok (.data 152 7 (.data 151 9 [] :: fs))) :
    ∃ sig callee args s, cl = .callIndirect sig callee args ∧ f.sigDecls.lookup sig = some s ∧
      fs = [.values (callee :: args), .op (.sig s)] := by
  obtain ⟨hf, ho⟩ := instData_inv_names h
  rw [variantNames_CallIndirect_fmt] at hf
  rw [variantNames_CallIndirect_op] at ho
  have hn : instNames cl = ("CallIndirect", "CallIndirect") :=
    Prod.ext (Option.some.inj hf).symm (Option.some.inj ho).symm
  obtain ⟨sig, callee, args, rfl⟩ : ∃ sig callee args, cl = .callIndirect sig callee args := by
    cases cl <;> simp [instNames] at hn ⊢
  simp only [instData] at h
  cases hs : f.sigDecls.lookup sig with
  | none => rw [hs] at h; cases h
  | some s =>
    rw [hs] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨-, -, h3⟩ := mkVariant_eq_data h
    injection h3 with _ h4
    exact ⟨sig, callee, args, s, rfl, rfl, h4⟩

theorem ext_value_slice_unwrap_iff {ctx : Ctx} (st : LState) (vs : List Nat) (fs : List V) :
    externExtract ctx T.value_slice_unwrap (.values vs) st = .ok fs ↔
      ∃ x xs, vs = x :: xs ∧ fs = [.value x, .values xs] := by
  cases vs with
  | nil =>
    have : externExtract ctx T.value_slice_unwrap (.values []) st = .fail := rfl
    rw [this]; simp
  | cons x xs =>
    have : externExtract ctx T.value_slice_unwrap (.values (x :: xs)) st =
        .ok [.value x, .values xs] := rfl
    rw [this]; simp [eq_comm]

/-- The number of CLIF results of a `call_indirect` is its signature's number of returns
(`CtxInv.resTys`). -/
theorem callIndirect_results_length {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx)
    {ii : Nat} {info : IInfo} {sig callee : Nat} {args : List Nat} {s : Clif.Signature}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some (.callIndirect sig callee args))
    (hs : f.sigDecls.lookup sig = some s) : info.results.length = s.returns.length := by
  obtain ⟨tys, htys, -, hl⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, hs, Option.map_some, Option.some.injEq] at htys
  rw [hl, ← htys, List.length_map]

/-- The low 64 bits of the register holding an `i64` CLIF value are its bits. -/
theorem lo64_of_vholds {x : BitVec 64} {c : CV} (h : VHolds ⟨.i64, x⟩ c) : lo64 c = x := h

theorem call_ind_lowerInstOk {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} {sigs : List Clif.Signature} (hCR : IndCallsRefine env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {sig callee : Nat} {args : List Nat}
    {s : Clif.Signature} (hs : f.sigDecls.lookup sig = some s) (hin : s ∈ sigs)
    (h8 : s.params.length ≤ 8) {st st' : LState} {results : List Nat}
    (hres : results.length = s.returns.length)
    (hst' : st'.nextVreg = st.nextVreg + (sigRets s).length) :
    LowerInstOk isem MR env cp ctx (.callIndirect sig callee args) results st
      (outRegs' st.nextVreg (sigRets s).length) st'
      [.call ⟨.reg (.vreg callee .int), retPairs (args.zip ((abiArgIdx s.params 0).map Reg.x)),
        callDefs (outDefs st.nextVreg (sigRets s).length)⟩] := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    simp only [List.mem_singleton] at hm
    subst hm
    rw [vdefs_call_reg] at hd
    simp only [outDefs, List.map_map, List.mem_map, List.mem_range, Function.comp_def] at hd
    obtain ⟨j, hj, rfl⟩ := hd
    omega
  · intro fr cm ρ w hfr hvh _ hmr
    split
    · rename_i rvals cm' hO
      obtain ⟨declared, x, vals, name, g, hd, hcv, hvals, hsym, hg, hty, hgo, hrty⟩ :=
        Driver.instOutcome_callIndirect_ok hO
      rw [hfr, hctx.func, hs] at hd
      cases hd
      have hvl : vals.length = s.params.length := by
        have := congrArg List.length hty; simpa [Clif.AbiParam.tys] using this
      have hal : args.length = s.params.length := (getMany_ok hvals).1 ▸ hvl
      have hrN : rvals.length = s.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      have hfst : (args.zip ((abiArgIdx s.params 0).map Reg.x)).map (·.1) = args :=
        List.map_fst_zip (by simp [abiArgIdx_length]; omega)
      have huses : (args.zip ((abiArgIdx s.params 0).map Reg.x)).map (ρ ·.1) = args.map ρ := by
        rw [show (fun x : Nat × Reg => ρ x.1) = ρ ∘ (·.1) from rfl, ← List.map_map, hfst]
      have hdl : (callDefs (outDefs st.nextVreg (sigRets s).length)).length =
          (sigRets s).length := by
        simp [callDefs, outDefs]
      have hlo : lo64 (ρ callee) = BitVec.ofNat 64 x.toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact lo64_of_vholds (hvh callee _ (get_regs hcv))
      obtain ⟨hcall, -⟩ := hCR
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall s hin name g fr.slots cm w x.toNat
        (.vreg callee .int) (retPairs (args.zip ((abiArgIdx s.params 0).map Reg.x)))
        (callDefs (outDefs st.nextVreg (sigRets s).length)) (ρ callee) (args.map ρ) vals rvals cm'
        hg hsym hlo hdl (by omega) (allHold_args hvh hvals) hmr hgo hrN
      have hol' : outs.length = (outDefs st.nextVreg (sigRets s).length).length := by
        rw [hol]; simp [callDefs, outDefs]
      rw [← huses] at hi
      refine ⟨?_, _, _, seqRun_call_reg hi hol', results_call hrN hres (by rw [hol, hdl]) hro,
        hmr'⟩
      intro mi hmi u hu
      simp only [List.mem_singleton] at hmi
      subst hmi
      rw [vuseNums_call_reg, hfst] at hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact .inr (by rw [get_regs hcv]; rfl)
      · exact .inr (usesOk_args hvals u hu)
    · intro h; simp [explicitTrapInst] at h
    · trivial

set_option maxHeartbeats 5000000 in
theorem call_ind_ruleOk {p : Program} (hp : Data p) (hpI : IndData p) {F : BitVec 64 → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sigs : List Clif.Signature} (hCR : IndCallsRefine env sigs MR isem) :
    IndRuleOk isem MR env cp sigs p rule_lower_2529 := by
  intro f ctx hctx ii info inst hi hcl hsig cfg hc m n st tr env' s1 out st' tr' hm hn hvb _ hmatch
    heval
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
  obtain ⟨hin, h8'⟩ := hsig sig callee args s rfl hs
  have hres := callIndirect_results_length hctx hi hcl hs
  simp only [ext_value_list_slice_iff, ext_value_slice_unwrap_iff] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2529] at heval
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
  have h8 : bytes.length ≤ 8 := sigParamBytes_length hb ▸ h8'
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg _ _ ‹ctx.valueReg? callee = some _›
  subst htgt
  simp only [ctor_gen_call_args_iff _ _ _ hb h8, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_ind_info_iff _ _ _ _ _ _ hb h8, Nat.reduceEqDiff, Nat.reduceLT,
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
  rw [uses_retPairs, callDefs_outDefs] at hs2
  rw [outRegs_eq]
  refine ⟨_, ?_, _, rfl, call_ind_lowerInstOk hCR hctx hs hin h8' hres
    (by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshN_emitted]

end Backend.Proof
