import FV.Backend.Proof.IselCtlTry
import FV.Backend.Proof.IselCtlCallInd

/-!
# Family Ctl: the `try_call_indirect` rule (the normal return)

`TryIndRuleOk` for `rule_lower_2561` (`blr` of the callee value's register, rule id 1036) of
`lower_branch`: as the GOT `try_call` rule (`try_got_ruleOk`, rule 1035) with the callee value's
vreg (`put_in_reg`) as the target and the exception table's signature as the ABI, under the
indirect-call contract `IndCallsRefine` (as the `call_indirect` rule, `call_ind_ruleOk`).
`tryIndUnmatchable`: the other rules of `lower_branch` name another format.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## ISLE data of the `try_call_indirect` rule -/

@[isel_data] theorem term_266_kind : T.«exception_sig».kind =
    (.decl ⟨false, false, false, false⟩ none (some (.external "exception_sig" true))) := rfl
@[isel_data] theorem term_266_name : T.«exception_sig».name = "exception_sig" := rfl
@[isel_data] theorem term_2298_kind : T.«Opcode.TryCallIndirect».kind = (.enumVariant 14) := rfl
@[isel_data] theorem term_2298_name :
    T.«Opcode.TryCallIndirect».name = "Opcode.TryCallIndirect" := rfl
@[isel_data] theorem term_2475_kind : T.«InstructionData.TryCallIndirect».kind =
    (.enumVariant 28) := rfl
@[isel_data] theorem term_2475_name :
    T.«InstructionData.TryCallIndirect».name = "InstructionData.TryCallIndirect" := rfl

/-- The term facts of the `try_call_indirect` rule beyond `Data`, `TryData` and `IndData`. -/
structure TryIndData (p : Program) : Prop where
  t266 : Interp.termOf p 266 = pure T.«exception_sig»
  t2298 : Interp.termOf p 2298 = pure T.«Opcode.TryCallIndirect»
  t2475 : Interp.termOf p 2475 = pure T.«InstructionData.TryCallIndirect»

theorem tryIndData_program : TryIndData program := ⟨rfl, rfl, rfl⟩

theorem ext_exception_sig_iff {ctx : Ctx} (st : LState) (s : Clif.Signature)
    (items : List (Option Nat)) (fs : List V) :
    externExtract ctx T.exception_sig (.op (.exnTable s items)) st = .ok fs ↔ fs = [.op (.sig s)] := by
  have : externExtract ctx T.exception_sig (.op (.exnTable s items)) st = .ok [.op (.sig s)] := rfl
  rw [this]
  constructor
  · intro h; cases h; rfl
  · rintro rfl; rfl

/-! ## The call of a `try_call_indirect` -/

theorem try_ind_lowerTryOk {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    {sigs : List Clif.Signature} (hCR : IndCallsRefine env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hctx : CtxInv f ctx) {callee : Nat} {args : List Nat}
    {et : Clif.ExnTable} {sig : Clif.Signature} (hsd : f.sigDecls.lookup et.sig = some sig)
    (hin : sig ∈ sigs) (h8 : sig.params.length ≤ 8) {info : TryInfo} {b : Nat}
    (htr : ctx.tryRegs = ((List.range (sigRets sig).length).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int]))
    {st st' : LState} (hst' : st'.nextVreg = st.nextVreg) :
    LowerTryOk isem MR env cp ctx (.callIndirect et.sig callee args) info st st'
      [.call ⟨.reg (.vreg callee .int), retPairs (args.zip ((abiArgIdx sig.params 0).map Reg.x)),
        callDefs (outDefs b (max (sigRets sig).length 2))⟩] := by
  refine ⟨by omega, ⟨[], _, rfl, by simp, fun d hd => ?_⟩, ?_⟩
  · rw [vdefs_call_reg] at hd
    exact tryDefs_mem htr d hd
  · intro fr cm ρ w hfr hvh _ hmr
    split
    · rename_i rvals cm' hO
      obtain ⟨declared, x, vals, name, g, hd, hcv, hvals, hsym, hg, hty, hgo, hrty⟩ :=
        Driver.instOutcome_callIndirect_ok hO
      rw [hfr, hctx.func, hsd] at hd
      cases hd
      have hvl : vals.length = sig.params.length := by
        have := congrArg List.length hty; simpa [Clif.AbiParam.tys] using this
      have hal : args.length = sig.params.length := (getMany_ok hvals).1 ▸ hvl
      have hrN : rvals.length = sig.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      have hfst : (args.zip ((abiArgIdx sig.params 0).map Reg.x)).map (·.1) = args :=
        List.map_fst_zip (by simp [abiArgIdx_length]; omega)
      have huses : (args.zip ((abiArgIdx sig.params 0).map Reg.x)).map (ρ ·.1) = args.map ρ := by
        rw [show (fun x : Nat × Reg => ρ x.1) = ρ ∘ (·.1) from rfl, ← List.map_map, hfst]
      have hdl : (callDefs (outDefs b (max (sigRets sig).length 2))).length =
          max (sigRets sig).length 2 := by
        simp [callDefs, outDefs]
      have hlo : lo64 (ρ callee) = BitVec.ofNat 64 x.toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact lo64_of_vholds (hvh callee _ (frame_get_regs hcv))
      obtain ⟨-, htry⟩ := hCR
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry sig hin name g fr.slots cm w x.toNat
        (.vreg callee .int) (retPairs (args.zip ((abiArgIdx sig.params 0).map Reg.x)))
        (callDefs (outDefs b (max (sigRets sig).length 2))) info (ρ callee) (args.map ρ) vals
        rvals cm' hg hsym hlo (by rw [hdl]; exact Nat.le_max_left _ _) (by omega)
        (allHold_args hvh hvals) hmr hgo hrN
      have hol' : outs.length = (outDefs b (max (sigRets sig).length 2)).length := by
        rw [hol, hdl]; simp [outDefs]
      rw [← huses] at hi
      rw [show ∀ c : CallInfo, tryFix info [MInst.call c] = [MInst.tryCall c info] from
        fun c => tryFix_append info [] c]
      refine ⟨?_, 0, _, _, ρ, w, outs, w', seqRun_tryCall_reg hi hol', rfl,
        fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
        simp only [List.mem_singleton] at hmi
        subst hmi
        rw [vuseNums_call_reg, hfst] at hu
        rcases List.mem_cons.mp hu with rfl | hu
        · exact .inr (by rw [frame_get_regs hcv]; rfl)
        · exact .inr (usesOk_args hvals u hu)
      · obtain ⟨-, rfl⟩ := tryRets_get htr hr
        refine ⟨b + j, rfl, ?_⟩
        rw [vdefUpd_call_reg]
        exact retsHeld_try (by rw [hol', outDefs, List.length_map, List.length_range]) hro hv
    · trivial

set_option maxHeartbeats 20000000 in
theorem try_ind_ruleOk {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) {F : BitVec 64 → Prop} {isem : Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR) {sigs : List Clif.Signature}
    (hCR : IndCallsRefine env sigs MR isem) :
    TryIndRuleOk isem MR env cp sigs p rule_lower_2561 := by
  intro f ctx hctx ti callee args et data sig items targets info lo st1 hd he hsig h8' hi hinfo htr
    hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  rw [tryCallIndData_eq he] at hd
  cases hd
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  obtain ⟨t196, t2293, t2454⟩ := hpI
  obtain ⟨t266, t2298, t2475⟩ := hpJ
  ctl_inv [*, rule_lower_2561, ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff, ctor_put_in_reg_iff] at hmatch heval
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff, ext_value_list_slice_iff,
    ctor_put_in_regs_vec_iff, ctor_put_in_reg_iff] at * <;> isel_destruct <;> subst_vars)
  have hti' := ‹tryInfoOf sig items targets = some _›
  rw [hinfo] at hti'
  cases hti'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  have h8 : bytes.length ≤ 8 := sigParamBytes_length hb ▸ h8'
  have hrs := mapM_valueReg hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg _ _ ‹ctx.valueReg? callee = some _›
  subst htgt
  simp only [ctor_gen_call_args_iff _ _ _ hb h8, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_ind_info_iff _ _ _ _ _ _ hb h8, Option.some.injEq] at *
  isel_destruct; subst_vars
  obtain ⟨hr8, rfl⟩ := retRegs_eq ‹retRegs _ = some _›
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
  rw [htrs, exnTableOpnd_cc he, tryDefs_eq _ _ hr8] at hs2
  rw [uses_retPairs] at hs2
  have hcd : ((List.range (max (sigRets sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine ⟨_, ?_, try_ind_lowerTryOk hCR hctx (exnTableOpnd_sig he) hsig h8' htrs
    (by rw [hs2, hs1]; simp [LState.emit])⟩
  rw [hs2, hs1]; simp [LState.emit]

/-! ## Assembly -/

theorem mem_lower_branch_2561 : rule_lower_2561 ∈ program.rulesOf TId.lower_branch := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  simp

/-- **`TryIndRulesCorrect`**: under the indirect-call contract, the `try_call_indirect` rule of
`lower_branch` (rule id 1036) is correct. -/
theorem tryIndRulesCorrect : TryIndRulesCorrect program := by
  intro F isem MR env cp sigs hR hMR hCR r hr hroot
  simp only [tryIndRootRule, beq_iff_eq] at hroot
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2561 (by rw [hroot]; rfl)]
  exact try_ind_ruleOk data_program tryData_program indData_program tryIndData_program hR hMR hCR

/-- The root format of the rules of `lower_branch` other than the `try_call_indirect` rule is
not `TryCallIndirect` (2475). -/
def tryIndFmtOk (r : Rule) : Bool :=
  tryIndRootRule r ||
    match ruleFmt r with
    | some fT => 2447 ≤ fT && fT < 2447 + 36 && fT != 2475
    | none => false

theorem lower_branch_tryInd_fmts : (program.rulesOf TId.lower_branch).all tryIndFmtOk = true := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  decide +kernel

/-- **`TryIndUnmatchable`**: no rule of `lower_branch` other than 1036 matches a
`try_call_indirect`. -/
theorem tryIndUnmatchable : TryIndUnmatchable program := by
  intro r hr hroot f ctx hctx ti callee args et data targets hd hi cfg m s env' s1 hmatch
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

end Backend.Proof
