import FV.Backend.Proof.IselCtlTryInd
import FV.Backend.Proof.IselCtlCallTI
import FV.Backend.Proof.IselTermIntPos
import FV.Backend.Proof.LowerContractTP

/-!
# Family Ctl over typed contexts: the `try_call` and `try_call_indirect` rules (S11e5 Stage C,
slice 5)

`try_call` (`bl`, rule 1034; GOT + `blr`, rule 1035) and `try_call_indirect` (1036) of
`lower_branch` over typed contexts (`CtxT`), on terminators whose integer operands (the callee
and the arguments) are in integer positions (`TermIntPos`; on a typed-scope function every
terminator's, `termIntPos_of`). The proofs are the integer ones (`IselCtlTry`, `IselCtlTryInd`)
with the arguments' and the callee's registers integer vregs by `TermIntPos`
(`mapM_valueRegTI`, `CtxInvT.valueReg_int`) and `CtxInvT.func`.

Results, for the pinned families of `LowerContractTP` (`TryRulesCorrectTP`,
`TryIndRulesCorrectTP`: the pinned `TryRuleOkP`/`TryIndRuleOkP` over `CtxT` with
`TermIntPos`): `tryRulesCorrectTP_program`, `tryIndRulesCorrectTP_program`; the unpinned
`tryRulesCorrectT_program`, `tryIndRulesCorrectT_program` (`tryRulesCorrectT_of_P`,
`tryIndRulesCorrectT_of_P`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## `try_call`: `bl` and GOT + `blr` -/

theorem try_sym_lowerTryOkT {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc} (hCR : CallsRefineP Pc F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat}
    {ext : Clif.ExtFunc} (hext : f.extern? fn = some ext) (hin : ext ∈ exts)
    (hso : SigStackOk ext.sig outB) {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes)
    {locs : List ArgLoc} {S : Nat} (hl : sigArgLocs ext.sig = .ok (locs, S)) {info : TryInfo}
    (hrets : info.rets ≤ (sigRets ext.sig).length) {b : Nat}
    (htr : ctx.tryRegs = ((List.range (sigRets ext.sig).length).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int]))
    {st st' : LState} (hst' : st'.nextVreg = st.nextVreg) :
    LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
        [.call ⟨.sym ext.name, retPairs (regPairsOf ((locs.zip args).zip bytes)),
          callDefs (outDefs b (max (sigRets ext.sig).length 2))⟩]) := by
  refine ⟨by omega, ⟨(stackEnts ((locs.zip args).zip bytes)).map argStore, _, rfl, ?_,
    fun d hd => ?_⟩, ?_⟩
  · intro m hm d hd
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
    simp [vdefs_argStore] at hd
  · rw [vdefs_call_sym] at hd
    exact tryDefs_mem htr d hd
  · intro fr cm ρ w hfr hvh _ hmr _ hpin
    split
    · rename_i rvals cm' hO
      obtain ⟨ext', vals, g, hx, hvals, hty, hg, hgo, hrty⟩ := instOutcome_call_ok hO
      have hx0 := hx
      rw [hfr, hfunc, hext] at hx
      cases hx
      have hpc := hpin.1 fn args ext vals g rvals cm' rfl hx0 hvals hg hgo
      have hrN : rvals.length = ext.sig.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      obtain ⟨hlen, hvx⟩ := getMany_ok hvals
      obtain ⟨w1, hrun1, hmr1, hargsAt⟩ := argsAt_after_stores hMR hMem hout hso hb hl hty
        hlen.symm (fun j v x hv hx => hvh x v (hvx j x v hx hv)) hmr
      obtain ⟨sym, -, -, htry⟩ := hCR
      have hdl : (callDefs (outDefs b (max (sigRets ext.sig).length 2))).length =
          max (sigRets ext.sig).length 2 := by
        simp [callDefs, outDefs]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w1 (.sym ext.name)
        (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs b (max (sigRets ext.sig).length 2))) info
        _ _ vals rvals cm' hg (.inl ⟨rfl, rfl⟩) (by rw [hdl]; exact Nat.le_max_left _ _) hrets
        (hargsAt w1 (SameWorldNF.refl F w1)) hmr1 hpc hgo hrN
      have hol' : outs.length = (outDefs b (max (sigRets ext.sig).length 2)).length := by
        rw [hol, hdl]; simp [outDefs]
      rw [tryFix_append]
      refine ⟨?_, _, _, _, _, _, outs, w',
        seqRun_append_fall_stop isem hrun1 (seqRun_tryCall_sym hi hol'), by simp,
        fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
        rcases List.mem_append.mp hmi with hmi | hmi
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
          rw [vuseNums_argStore, List.mem_singleton] at hu
          subst hu
          exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
        · simp only [List.mem_singleton] at hmi
          subst hmi
          rw [vuseNums_call_sym] at hu
          exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
      · obtain ⟨-, rfl⟩ := tryRets_get htr hr
        refine ⟨b + j, rfl, ?_⟩
        rw [vdefUpd_call]
        exact retsHeld_try (by rw [hol', outDefs, List.length_map, List.length_range]) hro hv
    · trivial

set_option maxHeartbeats 5000000 in
/-- **`try_call` by `bl`** (`rule_lower_2542`) over typed contexts. -/
theorem try_bl_ruleOkT {p : Program} (hp : Data p) (hpT : TryData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) :
    TryRuleOkTP Rd Pc isem MR env cp exts outB p rule_lower_2542 := by
  intro f ctx hctxT hexts ti fn args et data sig items targets info lo st1 hreg hd hip he hi hinfo
    htr hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst _ hmatch heval
  have hctx := hctxT.inv
  have hops : ∀ x ∈ args, IntPos ctx x := fun x hx => hip x (by simpa [Compile.termIntOperands])
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
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
  rw [hctx.func, hext] at hx'
  cases hx'
  have hti' := ‹tryInfoOf ext.sig items targets = some _›
  rw [hinfo] at hti'
  cases hti'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegTI hctx hops ‹List.mapM ctx.valueReg? args = some _›
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
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
  rw [htrs, exnTableOpnd_cc he, tryDefs_eq _ _ hr8] at hs2
  have hcd : ((List.range (max (sigRets ext.sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine ⟨_, ?_, try_sym_lowerTryOkT hMR hMem hout hCR hctx.func hext (hexts fn _ hext)
    (hreg _ hext) hb hl (Nat.le_of_eq (tryInfoOf_rets hinfo)) htrs
    (by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshN_emitted]

theorem try_got_lowerTryOkT {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc} (hCR : CallsRefineP Pc F env exts MR isem)
    {f : Clif.Function}
    {ctx : Ctx} (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hcol : ext.colocated = false)
    (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S)) {info : TryInfo}
    (hrets : info.rets ≤ (sigRets ext.sig).length) {b : Nat}
    (htr : ctx.tryRegs = ((List.range (sigRets ext.sig).length).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int]))
    {st st' : LState} (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + 1) :
    LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
       [.loadExtNameGot (.vreg st.nextVreg .int) ext.name,
       .call ⟨.reg (.vreg st.nextVreg .int),
        retPairs (regPairsOf ((locs.zip args).zip bytes)),
        callDefs (outDefs b (max (sigRets ext.sig).length 2))⟩]) := by
  refine ⟨by omega, ⟨(stackEnts ((locs.zip args).zip bytes)).map argStore ++
    [.loadExtNameGot (.vreg st.nextVreg .int) ext.name], _, by rw [List.append_assoc]; rfl, ?_,
    ?_⟩, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStore] at hd
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [vdefs_got_ctl] at hd
      simp only [List.mem_singleton] at hd
      omega
  · intro d hd
    rw [vdefs_call_reg] at hd
    exact tryDefs_mem htr d hd
  · intro fr cm ρ w hfr hvh _ hmr _ hpin
    split
    · rename_i rvals cm' hO
      obtain ⟨ext', vals, g, hx, hvals, hty, hg, hgo, hrty⟩ := instOutcome_call_ok hO
      have hx0 := hx
      rw [hfr, hfunc, hext] at hx
      cases hx
      have hpc := hpin.1 fn args ext vals g rvals cm' rfl hx0 hvals hg hgo
      have hrN : rvals.length = ext.sig.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      obtain ⟨hlen, hvx⟩ := getMany_ok hvals
      obtain ⟨w1, hrun1, hmr1, hargsAt⟩ := argsAt_after_stores hMR hMem hout hso hb hl hty
        hlen.symm (fun j v x hv hx => hvh x v (hvx j x v hx hv)) hmr
      obtain ⟨sym, hgot, -, htry⟩ := hCR
      obtain ⟨w2, hw2, hsw⟩ := hgot (.vreg st.nextVreg .int) ext.name w1
      have hmr2 := hMR _ _ _ _ hsw hmr1
      have hrun2 := seqRun_got (F := F) (ρ := ρ) hw2
      generalize ht : st.nextVreg = t at hrun2 hw2 hsw hargs ⊢
      have hρ1 : ∀ x ∈ args, upd ρ t (ofX (sym ext.name)) x = ρ x := by
        intro x hx
        have := hargs x hx
        simp only [upd]
        rw [if_neg (by omega)]
      have huses : (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1) =
          (regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1) := by
        apply List.map_congr_left
        intro q hq
        exact hρ1 _ (map_zip_args (mem_args_of_regPairs (List.mem_map_of_mem hq)))
      have hdl : (callDefs (outDefs b (max (sigRets ext.sig).length 2))).length =
          max (sigRets ext.sig).length 2 := by
        simp [callDefs, outDefs]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w2
        (.reg (.vreg t .int)) (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs b (max (sigRets ext.sig).length 2))) info
        (upd ρ t (ofX (sym ext.name)) t ::
          (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg
        (.inr ⟨_, rfl, hcol, by rw [ht1, huses]⟩) (by rw [hdl]; exact Nat.le_max_left _ _) hrets
        (hargsAt w2 hsw) hmr2 hpc hgo hrN
      have hol' : outs.length = (outDefs b (max (sigRets ext.sig).length 2)).length := by
        rw [hol, hdl]; simp [outDefs]
      have hrun3 := seqRun_tryCall_reg (info := info) hi hol'
      rw [show ∀ c : CallInfo, tryFix info ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
          [MInst.loadExtNameGot (.vreg t .int) ext.name, MInst.call c]) =
          ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
            [MInst.loadExtNameGot (.vreg t .int) ext.name]) ++ [MInst.tryCall c info]
        from fun c => by rw [← tryFix_append info _ c]; simp]
      refine ⟨?_, _, _, _, _, _, outs, w',
        seqRun_append_fall_stop isem (seqRun_append_fall' isem hrun1 hrun2) hrun3, by simp,
        fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
        rcases List.mem_append.mp hmi with hmi | hmi
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
          rw [vuseNums_argStore, List.mem_singleton] at hu
          subst hu
          exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmi
          rcases hmi with rfl | rfl
          · simp [vuseNums_got_ctl] at hu
          · rw [vuseNums_call_reg] at hu
            rcases List.mem_cons.mp hu with rfl | hu
            · exact .inl (by omega)
            · exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
      · obtain ⟨-, rfl⟩ := tryRets_get htr hr
        refine ⟨b + j, rfl, ?_⟩
        rw [vdefUpd_call_reg]
        exact retsHeld_try (by rw [hol', outDefs, List.length_map, List.length_range]) hro hv
    · trivial

set_option maxHeartbeats 20000000 in
/-- **`try_call` by GOT + `blr`** (`rule_lower_2551`) over typed contexts. -/
theorem try_got_ruleOkT {p : Program} (hp : Data p) (hpT : TryData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) :
    TryRuleOkTP Rd Pc isem MR env cp exts outB p rule_lower_2551 := by
  intro f ctx hctxT hexts ti fn args et data sig items targets info lo st1 hreg hd hip he hi hinfo
    htr hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst hfirst hmatch heval
  have hctx := hctxT.inv
  have hops : ∀ x ∈ args, IntPos ctx x := fun x hx => hip x (by simpa [Compile.termIntOperands])
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := ctx) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallData_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallData_eq he hext hsig] at hd
  cases hd
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  have hcol : ext.colocated = false := try_got_not_colocated hp hpT hi hfirst hfn
  clear hfirst
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
  rw [hctx.func, hext] at hx'
  cases hx'
  have hti' := ‹tryInfoOf ext.sig items targets = some _›
  rw [hinfo] at hti'
  cases hti'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hbelow := mapM_valueReg_below hvb ‹List.mapM ctx.valueReg? args = some _›
  have hrs := mapM_valueRegTI hctx hops ‹List.mapM ctx.valueReg? args = some _›
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
  obtain ⟨-, htrs, hst1, -⟩ := tryRegsOf_spec (exnTableOpnd_cc he) htr
  rw [htrs, exnTableOpnd_cc he, tryDefs_eq _ _ hr8] at hs2
  rw [show ∀ s : LState, (s.fresh .int).1 = .vreg s.nextVreg .int from fun s => rfl] at hs2 hs0
  have hcd : ((List.range (max (sigRets ext.sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets ext.sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs0 hs1 hs2
  refine ⟨_, ?_, try_got_lowerTryOkT hMR hMem hout hCR hctx.func hext (hexts fn _ hext) hcol
    (hreg _ hext) hb hl (Nat.le_of_eq (tryInfoOf_rets hinfo)) htrs
    (fun x hx => by have := hbelow x hx; omega)
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh]
  rw [← Array.toList_inj]
  simp

/-! ## `try_call_indirect` -/

theorem try_ind_lowerTryOkT {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    {sigs : List Clif.Signature} (hCR : IndCallsRefineP Pc env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hfunc : ctx.func = f) {callee : Nat} {args : List Nat}
    {et : Clif.ExnTable} {sig : Clif.Signature} (hsd : f.sigDecls.lookup et.sig = some sig)
    (hin : sig ∈ sigs) (hso : SigStackOk sig outB) {bytes : List Nat}
    (hb : sigParamBytes sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs sig = .ok (locs, S)) {info : TryInfo}
    (hrets : info.rets ≤ (sigRets sig).length) {b : Nat}
    (htr : ctx.tryRegs = ((List.range (sigRets sig).length).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int]))
    {st st' : LState} (hst' : st'.nextVreg = st.nextVreg) :
    LowerTryOkP Rd Pc isem MR env cp ctx (.callIndirect et.sig callee args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
        [.call ⟨.reg (.vreg callee .int), retPairs (regPairsOf ((locs.zip args).zip bytes)),
          callDefs (outDefs b (max (sigRets sig).length 2))⟩]) := by
  refine ⟨by omega, ⟨(stackEnts ((locs.zip args).zip bytes)).map argStore, _, rfl, ?_,
    fun d hd => ?_⟩, ?_⟩
  · intro m hm d hd
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
    simp [vdefs_argStore] at hd
  · rw [vdefs_call_reg] at hd
    exact tryDefs_mem htr d hd
  · intro fr cm ρ w hfr hvh _ hmr _ hpin
    split
    · rename_i rvals cm' hO
      obtain ⟨declared, x, vals, name, g, hd, hcv, hvals, hsym, hg, hsg, hty, hgo, hrty⟩ :=
        Driver.instOutcome_callIndirect_ok hO
      have hd0 := hd
      rw [hfr, hfunc, hsd] at hd
      cases hd
      have hpc := hpin.2 et.sig callee args sig x vals name g rvals cm' rfl hd0 hcv hvals hsym hg
        hgo hty
      have hrN : rvals.length = sig.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      obtain ⟨hlen, hvx⟩ := getMany_ok hvals
      obtain ⟨w1, hrun1, hmr1, hargsAt⟩ := argsAt_after_stores hMR hMem hout hso hb hl hty
        hlen.symm (fun j v x hv hx => hvh x v (hvx j x v hx hv)) hmr
      have hdl : (callDefs (outDefs b (max (sigRets sig).length 2))).length =
          max (sigRets sig).length 2 := by
        simp [callDefs, outDefs]
      have hlo : lo64 (ρ callee) = BitVec.ofNat 64 x.toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact lo64_of_vholds (hvh callee _ (frame_get_regs hcv))
      obtain ⟨-, htry⟩ := hCR
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry sig hin name g fr.slots cm w1 x.toNat
        (.vreg callee .int) (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs b (max (sigRets sig).length 2))) info (ρ callee)
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg hsg hsym hlo
        (by rw [hdl]; exact Nat.le_max_left _ _) hrets (hargsAt w1 (SameWorldNF.refl F w1)) hmr1
        hpc hgo hrN hty
      have hol' : outs.length = (outDefs b (max (sigRets sig).length 2)).length := by
        rw [hol, hdl]; simp [outDefs]
      rw [tryFix_append]
      refine ⟨?_, _, _, _, _, _, outs, w',
        seqRun_append_fall_stop isem hrun1 (seqRun_tryCall_reg hi hol'), by simp,
        fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
        rcases List.mem_append.mp hmi with hmi | hmi
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
          rw [vuseNums_argStore, List.mem_singleton] at hu
          subst hu
          exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
        · simp only [List.mem_singleton] at hmi
          subst hmi
          rw [vuseNums_call_reg] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact .inr (by rw [frame_get_regs hcv]; rfl)
          · exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
      · obtain ⟨-, rfl⟩ := tryRets_get htr hr
        refine ⟨b + j, rfl, ?_⟩
        rw [vdefUpd_call_reg]
        exact retsHeld_try (by rw [hol', outDefs, List.length_map, List.length_range]) hro hv
    · trivial

set_option maxHeartbeats 20000000 in
/-- **`try_call_indirect`** (`rule_lower_2561`) over typed contexts. -/
theorem try_ind_ruleOkT {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env}
    {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {sigs : List Clif.Signature} (hIstk : IndStack sigs outB)
    (hCR : IndCallsRefineP Pc env sigs MR isem) :
    TryIndRuleOkTP Rd Pc isem MR env cp sigs p rule_lower_2561 := by
  intro f ctx hctxT ti callee args et data sig items targets info lo st1 hd hip he hsig hi hinfo
    htr hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst _ hmatch heval
  have hctx := hctxT.inv
  have hops : ∀ x ∈ callee :: args, IntPos ctx x := fun x hx =>
    hip x (by simpa [Compile.termIntOperands] using hx)
  have hint := (sigIntB_iff.mp (exnTableOpnd_int he)).1
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
  have hsI := exnTableOpnd_int he
  try have hsE : sigIntB ext.sig = true := by first | (rw [hsig]; exact hsI) | exact hsI
  ctl_inv [*, rule_lower_2561, ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff hsI, ctor_put_in_reg_iff] at hmatch heval
  simp only [hi, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_value_slice_unwrap_iff, ext_exception_sig_iff, ctor_abi_sig_iff,
    ctor_try_call_info_iff, ctor_gen_try_call_rets_iff hsI, ext_value_list_slice_iff,
    ctor_put_in_regs_vec_iff, ctor_put_in_reg_iff] at * <;> isel_destruct <;> subst_vars)
  have hti' := ‹tryInfoOf sig items targets = some _›
  rw [hinfo] at hti'
  cases hti'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegTI hctx (fun x hx => hops x (List.mem_cons_of_mem _ hx))
    ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg_int ‹ctx.valueReg? callee = some _› (hops callee List.mem_cons_self)
  subst htgt
  simp only [ctor_gen_call_args_gen _ _ _ hb hl, mapM_single_map, Option.some.injEq,
    exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Option.some.injEq] at *
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
  have hcd : ((List.range (max (sigRets sig).length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max (sigRets sig).length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine ⟨_, ?_, try_ind_lowerTryOkT hMR hMem hout hCR hctx.func (exnTableOpnd_sig he) hsig
    (hIstk sig hsig) hb hl (Nat.le_of_eq (tryInfoOf_rets hinfo)) htrs
    (by rw [hs2, hs1]; simp [LState.emit])⟩
  rw [hs2, hs1]; simp [LState.emit]

/-! ## Assembly -/

/-- **`TryRulesCorrectTP`**: under the pinned callee contract and the guarded memory forms, the
`try_call` rules of `lower_branch` (1034, 1035) are correct over typed contexts. -/
theorem tryRulesCorrectTP_program : TryRulesCorrectTP program := by
  intro Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR r hr hroot
  simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  rcases hroot with h | h
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2542 (by rw [h]; rfl)]
    exact try_bl_ruleOkT data_program tryData_program hR hMR hMem hout hCR
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2551 (by rw [h]; rfl)]
    exact try_got_ruleOkT data_program tryData_program hR hMR hMem hout hCR

/-- **`TryIndRulesCorrectTP`**: under the pinned indirect-call contract, guarded memory forms and
an outgoing area holding the stack arguments (S5), the `try_call_indirect` rule of
`lower_branch` (1036) is correct over typed contexts. -/
theorem tryIndRulesCorrectTP_program : TryIndRulesCorrectTP program := by
  intro Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR r hr hroot
  simp only [tryIndRootRule, beq_iff_eq] at hroot
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2561 (by rw [hroot]; rfl)]
  exact try_ind_ruleOkT data_program tryData_program indData_program tryIndData_program hR hMR
    hMem hout hIstk hCR

/-- **`TryRulesCorrectT`** (`tryRulesCorrectTP_program` with nothing pinned). -/
theorem tryRulesCorrectT_program : TryRulesCorrectT program :=
  tryRulesCorrectT_of_P tryRulesCorrectTP_program

/-- **`TryIndRulesCorrectT`** (`tryIndRulesCorrectTP_program` with nothing pinned). -/
theorem tryIndRulesCorrectT_program : TryIndRulesCorrectT program :=
  tryIndRulesCorrectT_of_P tryIndRulesCorrectTP_program

end Backend.Proof
