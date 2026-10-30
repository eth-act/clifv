import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.IselCtlCallInd
import FV.Backend.Proof.IselMemBaseTI
import FV.Backend.Proof.LowerContractTP

/-!
# Family Ctl over typed contexts: the call rules (S11e5 Stage C, slice 5)

The `call` rules of `lower` (`bl`, rule 1031; GOT + `blr`, rule 1032) and the `call_indirect`
rule (1033) over typed contexts (`CtxT`), on subset-E instructions (calls are integer-only in
the typed scope: integer externs, `instData`'s `sigIntB`). The proofs are the integer ones
(`IselCtlCallRules`, `IselCtlCallInd`) with:

* the arguments' (and the callee's) registers integer vregs because they are in integer
  positions (`intArgs`, `CtxInvT.intOps`: `mapM_valueRegTI`, `CtxInvT.valueRegI`), not because
  every value is an integer;
* the call's returns of class `int` because its result types are E's (`CtxT.resTysE`:
  `CtxT.call_retClasses`);
* `CtxInvT.func`/`data`/`resTys` in place of `CtxInv`'s.

Results, for the pinned families of `LowerContractTP` (`CallRulesCorrectTP`,
`IndRulesCorrectTP`: the pinned `CallRuleOkP`/`IndRuleOkP` over `CtxT`, subset-E instructions):
`callRulesCorrectTP_program`, `indRulesCorrectTP_program`; the unpinned
`callRulesCorrectT_program`, `indRulesCorrectT_program` (`callRulesCorrectT_of_P`,
`indRulesCorrectT_of_P`).
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000

/-! ## Typed-context facts -/

/-- The registers of values in integer positions of a float-capable context are integer
vregs. -/
theorem mapM_valueRegTI {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) :
    ∀ {xs : List Nat} {rs : List Reg}, (∀ x ∈ xs, IntPos ctx x) → xs.mapM ctx.valueReg? = some rs →
      rs = xs.map fun x => Reg.vreg x .int
  | [], rs, _, h => by simp at h; simp [h]
  | x :: xs, rs, hi, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs, rfl⟩ := h
    rw [hctx.valueReg_int hr (hi x List.mem_cons_self),
      mapM_valueRegTI hctx (fun y hy => hi y (List.mem_cons_of_mem _ hy)) hrs]
    rfl

/-- The number of CLIF results of a `call` is its callee's number of returns
(`call_results_length` over `CtxInvT`). -/
theorem call_results_lengthT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx) {ii : Nat}
    {info : IInfo} {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some (.call fn args))
    (hext : f.extern? fn = some ext) : info.results.length = ext.sig.returns.length := by
  obtain ⟨tys, htys, -, hl⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, hext, Option.map_some, Option.some.injEq] at htys
  rw [hl, ← htys, List.length_map]

/-- The number of CLIF results of a `call_indirect` (`callIndirect_results_length` over
`CtxInvT`). -/
theorem callIndirect_results_lengthT {f : Clif.Function} {ctx : Ctx} (hctx : CtxInvT f ctx)
    {ii : Nat} {info : IInfo} {sig callee : Nat} {args : List Nat} {s : Clif.Signature}
    (hi : ctx.insts[ii]? = some info) (hc : info.clif = some (.callIndirect sig callee args))
    (hs : f.sigDecls.lookup sig = some s) : info.results.length = s.returns.length := by
  obtain ⟨tys, htys, -, hl⟩ := hctx.resTys ii info _ hi hc
  simp only [Clif.Inst.resultTypes, hs, Option.map_some, Option.some.injEq] at htys
  rw [hl, ← htys, List.length_map]

/-- A subset-E `call` of a typed context returns integers (`CtxInv.call_retClasses` from
`CtxT.resTysE`). -/
theorem CtxT.call_retClasses {f : Clif.Function} {ctx : Ctx} (hctx : CtxT f ctx) {ii : Nat}
    {info : IInfo} {fn : Clif.FnRef} {args : List Nat} (hi : ctx.insts[ii]? = some info)
    (hcl : info.clif = some (.call fn args)) (hE : Compile.instE (.call fn args) = true)
    {e : Clif.ExtFunc} (he : f.extern? fn = some e) :
    (sigRets e.sig).map retClass = List.replicate (sigRets e.sig).length .int := by
  apply sigRets_classes_int
  obtain ⟨tys, hty, hres, -⟩ := hctx.inv.resTys ii info _ hi hcl
  simp only [Clif.Inst.resultTypes, he, Option.map_some, Option.some.injEq] at hty
  subst hty
  refine List.all_eq_true.mpr fun p hp => ?_
  have hm := hctx.resTysE hi hcl hE (CTy.ofClif p.ty)
    (by rw [hres]; exact List.mem_map_of_mem (List.mem_map_of_mem hp))
  cases hpt : p.ty <;> simp_all [eCTys, CTy.ofClif, Clif.Ty.isInt]

/-! ## `bl` and GOT + `blr` -/

theorem call_sym_lowerInstOkT {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc} (hCR : CallsRefineP Pc F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx}
    (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S))
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hst' : st'.nextVreg = st.nextVreg + (sigRets ext.sig).length) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.call fn args) results st
      (outRegs' st.nextVreg (sigRets ext.sig).length) st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
        [.call ⟨.sym ext.name, retPairs (regPairsOf ((locs.zip args).zip bytes)),
          callDefs (outDefs st.nextVreg (sigRets ext.sig).length)⟩]) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStore] at hd
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [vdefs_call_sym] at hd
      simp only [outDefs, List.map_map, List.mem_map, List.mem_range, Function.comp_def] at hd
      obtain ⟨j, hj, rfl⟩ := hd
      omega
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
      obtain ⟨w1, hrun1, hmr1, hargs⟩ := argsAt_after_stores hMR hMem hout hso hb hl hty hlen.symm
        (fun j v x hv hx => hvh x v (hvx j x v hx hv)) hmr
      obtain ⟨sym, -, hcall, -⟩ := hCR
      have hdl : (callDefs (outDefs st.nextVreg (sigRets ext.sig).length)).length =
          (sigRets ext.sig).length := by simp [callDefs, outDefs]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w1 (.sym ext.name)
        (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs st.nextVreg (sigRets ext.sig).length))
        _ _ vals rvals cm' hg (.inl ⟨rfl, rfl⟩) hdl (hargs w1 (SameWorldNF.refl F w1)) hmr1 hpc hgo
        hrN
      have hol' : outs.length = (outDefs st.nextVreg (sigRets ext.sig).length).length := by
        rw [hol]; simp [callDefs, outDefs]
      refine ⟨?_, _, _, seqRun_append_fall' isem hrun1 (seqRun_call_sym hi hol'),
        results_call hrN hres (by rw [hol, hdl]) hro, hmr'⟩
      intro mi hmi u hu
      rcases List.mem_append.mp hmi with hmi | hmi
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
        rw [vuseNums_argStore, List.mem_singleton] at hu
        subst hu
        exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
      · simp only [List.mem_singleton] at hmi
        subst hmi
        rw [vuseNums_call_sym] at hu
        exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
    · intro h; simp [explicitTrapInst] at h
    · trivial

theorem call_got_lowerInstOkT {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc} (hCR : CallsRefineP Pc F env exts MR isem)
    {f : Clif.Function}
    {ctx : Ctx} (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hcol : ext.colocated = false)
    (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S))
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + (sigRets ext.sig).length + 1) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.call fn args) results st
      (outRegs' st.nextVreg (sigRets ext.sig).length) st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
       [.loadExtNameGot (.vreg (st.nextVreg + (sigRets ext.sig).length) .int) ext.name,
       .call ⟨.reg (.vreg (st.nextVreg + (sigRets ext.sig).length) .int),
        retPairs (regPairsOf ((locs.zip args).zip bytes)),
        callDefs (outDefs st.nextVreg (sigRets ext.sig).length)⟩]) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStore] at hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · rw [vdefs_got_ctl] at hd
        simp only [List.mem_singleton] at hd
        omega
      · rw [vdefs_call_reg] at hd
        simp only [outDefs, List.map_map, List.mem_map, List.mem_range, Function.comp_def] at hd
        obtain ⟨j, hj, rfl⟩ := hd
        omega
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
      obtain ⟨sym, hgot, hcall, -⟩ := hCR
      obtain ⟨w2, hw2, hsw⟩ := hgot (.vreg (st.nextVreg + (sigRets ext.sig).length) .int) ext.name w1
      have hmr2 := hMR _ _ _ _ hsw hmr1
      have hrun2 := seqRun_got (F := F) (ρ := ρ) hw2
      generalize ht : st.nextVreg + (sigRets ext.sig).length = t at hrun2 hw2 hsw ⊢
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
      have hdl : (callDefs (outDefs st.nextVreg (sigRets ext.sig).length)).length =
          (sigRets ext.sig).length := by simp [callDefs, outDefs]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w2
        (.reg (.vreg t .int)) (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs st.nextVreg (sigRets ext.sig).length))
        (upd ρ t (ofX (sym ext.name)) t ::
          (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg
        (.inr ⟨_, rfl, hcol, by rw [ht1, huses]⟩) hdl (hargsAt w2 hsw) hmr2 hpc hgo hrN
      have hol' : outs.length = (outDefs st.nextVreg (sigRets ext.sig).length).length := by
        rw [hol]; simp [callDefs, outDefs]
      have hrun3 := seqRun_call_reg hi hol'
      refine ⟨?_, _, _, seqRun_append_fall' isem hrun1
          (seqRun_append_fall' isem (ms1 := [_]) (ms2 := [_]) hrun2 hrun3),
        results_call hrN hres (by rw [hol, hdl]) hro, hmr'⟩
      intro mi hmi u hu
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
    · intro h; simp [explicitTrapInst] at h
    · trivial

set_option maxHeartbeats 5000000 in
/-- **`bl`** (`rule_lower_2508`) over typed contexts. -/
theorem call_bl_ruleOkT {p : Program} (hp : Data p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) :
    CallRuleOkTP Rd Pc isem MR env cp exts outB p rule_lower_2508 := by
  intro f ctx hctxT hexts ii info inst hi hcl hE hstk cfg hc m n st tr env' s1 out st' tr' hm hn
    hvb _ hmatch heval
  have hctx := hctxT.inv
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
  have hres := call_results_lengthT hctx hi hcl hext
  have hrc := hctxT.call_retClasses hi hcl hE hext
  have hops : ∀ x ∈ args, IntPos ctx x := fun x hx => hctx.intOps ii info _ hi hcl x hx
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
  have hrs := mapM_valueRegTI hctx hops ‹List.mapM ctx.valueReg? args = some _›
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
  rw [outRegs_eq]
  refine ⟨_, ?_, _, rfl, call_sym_lowerInstOkT hMR hMem hout hCR hctx.func hext (hexts fn _ hext)
    (hstk fn args _ rfl hext) hb hl hres (by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshN_emitted]

set_option maxHeartbeats 5000000 in
/-- **GOT + `blr`** (`rule_lower_2518`) over typed contexts. -/
theorem call_got_ruleOkT {p : Program} (hp : Data p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefineP Pc F env exts MR isem) :
    CallRuleOkTP Rd Pc isem MR env cp exts outB p rule_lower_2518 := by
  intro f ctx hctxT hexts ii info inst hi hcl hE hstk cfg hc m n st tr env' s1 out st' tr' hm hn
    hvb hfirst hmatch heval
  have hctx := hctxT.inv
  have hnot : ∀ {fn : Nat} {args : List Nat} {ext : Clif.ExtFunc},
      info.data = .data 152 6 [.data 151 8 [], .values args, .op (.funcRef fn)] →
      ctx.func.extern? fn = some ext → ext.colocated = false :=
    fun hd he => call_got_not_colocated hp hi hfirst hd he
  clear hfirst
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
  have hcol : ext.colocated = false := hnot ‹V.data 152 6 _ = info.data›.symm hfn
  clear hnot
  have hres := call_results_lengthT hctx hi hcl hext
  have hrc := hctxT.call_retClasses hi hcl hE hext
  have hops : ∀ x ∈ args, IntPos ctx x := fun x hx => hctx.intOps ii info _ hi hcl x hx
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
  have hbelow := mapM_valueReg_below hvb ‹List.mapM ctx.valueReg? args = some _›
  have hrs := mapM_valueRegTI hctx hops ‹List.mapM ctx.valueReg? args = some _›
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
  have hfr : ∀ k (e : Array MInst), (({ freshN st k with emitted := e } : LState).fresh .int).1 =
      .vreg (st.nextVreg + k) .int := fun k e => by
    simp [LState.fresh, freshN_nextVreg]
  rw [hfr, callDefs_outDefs] at hs2
  rw [hfr] at hs0
  rw [outRegs_eq]
  refine ⟨_, ?_, _, rfl, call_got_lowerInstOkT hMR hMem hout hCR hctx.func hext (hexts fn _ hext)
    hcol (hstk fn args _ rfl hext) hb hl hres hbelow
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh, freshN_nextVreg])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh, freshN_emitted]
  rw [← Array.toList_inj]
  simp

/-! ## `call_indirect` -/

theorem call_ind_lowerInstOkT {Rd : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sigs : List Clif.Signature}
    (hCR : IndCallsRefineP Pc env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hfunc : ctx.func = f) {sig callee : Nat} {args : List Nat}
    {s : Clif.Signature} (hs : f.sigDecls.lookup sig = some s) (hin : s ∈ sigs)
    (h8 : s.params.length ≤ 8) {st st' : LState} {results : List Nat}
    (hres : results.length = s.returns.length)
    (hst' : st'.nextVreg = st.nextVreg + (sigRets s).length) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.callIndirect sig callee args) results st
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
  · intro fr cm ρ w hfr hvh _ hmr _ hpin
    split
    · rename_i rvals cm' hO
      obtain ⟨declared, x, vals, name, g, hd, hcv, hvals, hsym, hg, hsg, hty, hgo, hrty⟩ :=
        Driver.instOutcome_callIndirect_ok hO
      have hd0 := hd
      rw [hfr, hfunc, hs] at hd
      cases hd
      have hpc := hpin.2 sig callee args s x vals name g rvals cm' rfl hd0 hcv hvals hsym hg hgo hty
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
        exact lo64_of_vholds (hvh callee _ (frame_get_regs hcv))
      obtain ⟨hcall, -⟩ := hCR
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall s hin name g fr.slots cm w x.toNat
        (.vreg callee .int) (retPairs (args.zip ((abiArgIdx s.params 0).map Reg.x)))
        (callDefs (outDefs st.nextVreg (sigRets s).length)) (ρ callee) (args.map ρ) vals rvals cm'
        hg hsg hsym hlo hdl (by omega) (allHold_args hvh hvals) hmr hpc hgo hrN hty
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
      · exact .inr (by rw [frame_get_regs hcv]; rfl)
      · exact .inr (usesOk_args hvals u hu)
    · intro h; simp [explicitTrapInst] at h
    · trivial

set_option maxHeartbeats 5000000 in
/-- **`blr` of the callee value** (`rule_lower_2529`, `call_indirect`) over typed contexts. -/
theorem call_ind_ruleOkT {p : Program} (hp : Data p) (hpI : IndData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sigs : List Clif.Signature} (hCR : IndCallsRefineP Pc env sigs MR isem) :
    IndRuleOkTP Rd Pc isem MR env cp sigs p rule_lower_2529 := by
  intro f ctx hctxT ii info inst hi hcl _ hsig cfg hc m n st tr env' s1 out st' tr' hm hn hvb _
    hmatch heval
  have hctx := hctxT.inv
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
  have hint := (sigIntB_iff.mp (instData_callIndirect_int hd hs)).1
  have hrc := sigRets_classes_int (sigIntB_iff.mp (instData_callIndirect_int hd hs)).2
  have hops : ∀ x ∈ callee :: args, IntPos ctx x := fun x hx => hctx.intOps ii info _ hi hcl x hx
  simp only [List.cons.injEq, and_true] at hfs
  obtain ⟨rfl, rfl⟩ := hfs
  obtain ⟨hin, h8'⟩ := hsig sig callee args s rfl hs
  have hres := callIndirect_results_lengthT hctx hi hcl hs
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
  have h8 : bytes.length ≤ 8 := sigParamBytes_length hb ▸ h8'
  have hrs := mapM_valueRegTI hctx (fun x hx => hops x (List.mem_cons_of_mem _ hx))
    ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg_int ‹ctx.valueReg? callee = some _› (hops callee List.mem_cons_self)
  subst htgt
  simp only [ctor_gen_call_args_iff _ _ _ hint hb h8, mapM_single_map, Option.some.injEq,
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
  refine ⟨_, ?_, _, rfl, call_ind_lowerInstOkT hCR hctx.func hs hin h8' hres
    (by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshN_emitted]

/-! ## Assembly -/

/-- **`CallRulesCorrectTP`**: under the pinned callee contract and the guarded memory forms, the
`call` rules of `lower` (1031, 1032) are correct over typed contexts. -/
theorem callRulesCorrectTP_program : CallRulesCorrectTP program := by
  intro Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR r hr hroot
  simp only [callRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  rcases hroot with h | h
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2508 (by rw [h]; rfl)]
    exact call_bl_ruleOkT data_program hR hMR hMem hout hCR
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2518 (by rw [h]; rfl)]
    exact call_got_ruleOkT data_program hR hMR hMem hout hCR

/-- **`CallRulesCorrectT`** (`callRulesCorrectTP_program` with nothing pinned). -/
theorem callRulesCorrectT_program : CallRulesCorrectT program :=
  callRulesCorrectT_of_P callRulesCorrectTP_program

/-- **`IndRulesCorrectTP`**: under the pinned indirect-call contract, the `call_indirect` rule of
`lower` (1033) is correct over typed contexts. -/
theorem indRulesCorrectTP_program : IndRulesCorrectTP program := by
  intro Rd Pc F isem MR env cp sigs hR hMR hCR r hr hroot
  simp only [indRootRule, beq_iff_eq] at hroot
  rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2529 (by rw [hroot]; rfl)]
  exact call_ind_ruleOkT data_program indData_program hR hMR hCR

/-- **`IndRulesCorrectT`** (`indRulesCorrectTP_program` with nothing pinned). -/
theorem indRulesCorrectT_program : IndRulesCorrectT program :=
  indRulesCorrectT_of_P indRulesCorrectTP_program

end Backend.Proof
