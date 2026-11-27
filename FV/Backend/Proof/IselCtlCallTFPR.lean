import FV.Backend.Proof.IselContractPR

/-!
# The call rules with the call site's registers (#753, stage R1): float-capable contexts

The rule theorems of `IselCtlCallF` and `IselCtlTryF` (`CallCtxT` contexts, any extern signature)
under the contract with registers (`CallsRefinePR`, `IselContractPR`): the GOT calls also give the
contract the registers of the emitted site (`siteRegsR_callC`, `siteRegsR_tryC`: the arguments in
`E2E.regLocs` of the signature, the returns from `retRegsC` of their classes).
`call_got_lowerInstOkTFPR`, `try_got_lowerTryOkTFPR` (and `call_sym_lowerInstOkTFPR`,
`try_sym_lowerTryOkTFPR`); the rules `…_ruleOkTFPR`; the families `callRulesCorrectTFPR_program`,
`tryRulesCorrectTFPR_program`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000
set_option autoImplicit false

/-! ## The lowering of the call sites -/

theorem call_sym_lowerInstOkTFPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx}
    (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S)) {ps : List Reg}
    (hps : ps.length = (ext.sig.returns.map retClass).length)
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hst' : st'.nextVreg = st.nextVreg + ext.sig.returns.length) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.call fn args) results st
      (outRegsC st (ext.sig.returns.map retClass)) st'
      ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
        [.call ⟨.sym ext.name, argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))),
          callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass))⟩]) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStoreC] at hd
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [vdefs_call_symC, outDefsC_vregs _ hps] at hd
      simp only [List.length_map, List.mem_map, List.mem_range] at hd
      obtain ⟨j, hj, rfl⟩ := hd
      omega
  · intro fr cm ρ w hfr hvh hdfg hmr _ hpin
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
      obtain ⟨w1, hrun1, hmr1, hargs⟩ := argsAt_after_storesC hMR hMem hFP hout hso hb hl hty
        hlen.symm (valClassOf ctx) (fun j v x hv hx => hvh x v (hvx j x v hx hv))
        (argClasses_of_frame_sig hdfg hvals hty hso.2) hmr
      obtain ⟨sym, -, hcall, -⟩ := hCR
      have hdl : (callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass))).length =
          ext.sig.returns.length := by
        simp [callDefsC, outDefsC_length _ hps]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w1 (.sym ext.name)
        (argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))))
        (callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass)))
        _ _ vals rvals cm' hg (.inl ⟨rfl, rfl⟩) hdl (hargs w1 (SameWorldNF.refl F w1)) hmr1 hpc hgo
        hrN
      rw [← liftC_vals (valClassOf ctx)] at hi
      have hol' : outs.length = (outDefsC st.nextVreg ps (ext.sig.returns.map retClass)).length := by
        rw [hol, hdl, outDefsC_length _ hps, List.length_map]
      refine ⟨?_, _, _, seqRun_append_fall' isem hrun1 (seqRun_call_symC hi hol'),
        results_callC hps hrN hres (by rw [hol, hdl]) hro, hmr'⟩
      intro mi hmi u hu
      rcases List.mem_append.mp hmi with hmi | hmi
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
        rw [vuseNums_argStoreC, List.mem_singleton] at hu
        subst hu
        exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
      · simp only [List.mem_singleton] at hmi
        subst hmi
        rw [vuseNums_call_symC, liftC_fst] at hu
        exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
    · intro h; simp [explicitTrapInst] at h
    · trivial

theorem call_got_lowerInstOkTFPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) {f : Clif.Function}
    {ctx : Ctx} (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hcol : ext.colocated = false)
    (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S)) {ps : List Reg}
    (hps : ps.length = (ext.sig.returns.map retClass).length)
    (hps0 : retRegsC (ext.sig.returns.map retClass) 0 0 = some ps)
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + ext.sig.returns.length + 1) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.call fn args) results st
      (outRegsC st (ext.sig.returns.map retClass)) st'
      ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
       [.loadExtNameGot (.vreg (st.nextVreg + ext.sig.returns.length) .int) ext.name,
       .call ⟨.reg (.vreg (st.nextVreg + ext.sig.returns.length) .int),
        argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))),
        callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass))⟩]) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStoreC] at hd
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · rw [vdefs_got_ctl] at hd
        simp only [List.mem_singleton] at hd
        omega
      · rw [vdefs_call_regC, outDefsC_vregs _ hps] at hd
        simp only [List.length_map, List.mem_map, List.mem_range] at hd
        obtain ⟨j, hj, rfl⟩ := hd
        omega
  · intro fr cm ρ w hfr hvh hdfg hmr _ hpin
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
      obtain ⟨w1, hrun1, hmr1, hargsAt⟩ := argsAt_after_storesC hMR hMem hFP hout hso hb hl hty
        hlen.symm (valClassOf ctx) (fun j v x hv hx => hvh x v (hvx j x v hx hv))
        (argClasses_of_frame_sig hdfg hvals hty hso.2) hmr
      obtain ⟨sym, hgot, hcall, -⟩ := hCR
      obtain ⟨w2, hw2, hsw⟩ := hgot (.vreg (st.nextVreg + ext.sig.returns.length) .int) ext.name w1
      have hmr2 := hMR _ _ _ _ hsw hmr1
      have hrun2 := seqRun_got (F := F) (ρ := ρ) hw2
      generalize ht : st.nextVreg + ext.sig.returns.length = t at hrun2 hw2 hsw ⊢
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
      have hdl : (callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass))).length =
          ext.sig.returns.length := by
        simp [callDefsC, outDefsC_length _ hps]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w2
        (.reg (.vreg t .int)) (argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))))
        (callDefsC (outDefsC st.nextVreg ps (ext.sig.returns.map retClass)))
        (upd ρ t (ofX (sym ext.name)) t ::
          (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg
        (.inr ⟨_, rfl, hcol, by rw [ht1, huses],
          siteRegsR_callC hl hb (args_length_of hlen hty) _ hps0 _⟩) hdl (hargsAt w2 hsw) hmr2 hpc hgo hrN
      rw [← liftC_vals (valClassOf ctx)] at hi
      have hol' : outs.length = (outDefsC st.nextVreg ps (ext.sig.returns.map retClass)).length := by
        rw [hol, hdl, outDefsC_length _ hps, List.length_map]
      have hrun3 := seqRun_call_regC hi hol'
      refine ⟨?_, _, _, seqRun_append_fall' isem hrun1
          (seqRun_append_fall' isem (ms1 := [_]) (ms2 := [_]) hrun2 hrun3),
        results_callC hps hrN hres (by rw [hol, hdl]) hro, hmr'⟩
      intro mi hmi u hu
      rcases List.mem_append.mp hmi with hmi | hmi
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
        rw [vuseNums_argStoreC, List.mem_singleton] at hu
        subst hu
        exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmi
        rcases hmi with rfl | rfl
        · simp [vuseNums_got_ctl] at hu
        · rw [vuseNums_call_regC, liftC_fst] at hu
          rcases List.mem_cons.mp hu with rfl | hu
          · exact .inl (by omega)
          · exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
    · intro h; simp [explicitTrapInst] at h
    · trivial

theorem try_sym_lowerTryOkTFPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx}
    (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S)) {info : TryInfo}
    (hrets : info.rets ≤ ext.sig.returns.length) {b : Nat} {ps fp : List Reg}
    (hps : ps.length = (ext.sig.returns.map retClass).length)
    (htr : ctx.tryRegs.1 = (ext.sig.returns.map retClass).zipIdx.map fun q => Reg.vreg (b + q.2) q.1)
    (hdefs : ∀ d ∈ (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
      List.replicate fp.length .int)).map (·.2.1), ∃ c, Reg.vreg d c ∈ tryDefRegs ctx)
    {st st' : LState} (hst' : st'.nextVreg = st.nextVreg) :
    LowerTryOkPC Rd Pc isem MR env cp ctx (.call fn args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
        [.call ⟨.sym ext.name, argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))),
          callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
            List.replicate fp.length .int))⟩]) := by
  refine ⟨by omega, ⟨(stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)), _, rfl,
    ?_, fun d hd => ?_⟩, ?_⟩
  · intro m hm d hd
    obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
    simp [vdefs_argStoreC] at hd
  · rw [vdefs_call_symC] at hd
    exact hdefs d hd
  · intro fr cm ρ w hfr hvh hdfg hmr _ hpin
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
      obtain ⟨w1, hrun1, hmr1, hargs⟩ := argsAt_after_storesC hMR hMem hFP hout hso hb hl hty
        hlen.symm (valClassOf ctx) (fun j v x hv hx => hvh x v (hvx j x v hx hv))
        (argClasses_of_frame_sig hdfg hvals hty hso.2) hmr
      obtain ⟨sym, -, -, htry⟩ := hCR
      have hdl : (callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int))).length = ext.sig.returns.length + fp.length := by
        rw [callDefsC, List.length_map, outDefsC_app_length b hps, List.length_map]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w1 (.sym ext.name)
        (argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))))
        (callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int))) info
        _ _ vals rvals cm' hg (.inl ⟨rfl, rfl⟩) (by rw [hdl]; omega) hrets
        (hargs w1 (SameWorldNF.refl F w1)) hmr1 hpc hgo hrN
      rw [← liftC_vals (valClassOf ctx)] at hi
      have hol' : outs.length = (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int)).length := by
        rw [hol, callDefsC, List.length_map]
      rw [tryFix_append]
      refine ⟨?_, _, _, _, _, _, outs, w',
        seqRun_append_fall_stop isem hrun1 (seqRun_tryCall_symC hi hol'), by simp,
        fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
        rcases List.mem_append.mp hmi with hmi | hmi
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
          rw [vuseNums_argStoreC, List.mem_singleton] at hu
          subst hu
          exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
        · simp only [List.mem_singleton] at hmi
          subst hmi
          rw [vuseNums_call_symC, liftC_fst] at hu
          exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
      · obtain ⟨c, hc, rfl⟩ := tryRetsC_get htr hr
        refine ⟨b + j, c, rfl, ?_⟩
        rw [vdefUpd_callC]
        exact retsHeld_tryC hps (by rw [hol, hdl, List.length_map]) hro hv hc
    · trivial

theorem try_got_lowerTryOkTFPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) {f : Clif.Function} {ctx : Ctx}
    (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hcol : ext.colocated = false)
    (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S)) {info : TryInfo}
    (hrets : info.rets ≤ ext.sig.returns.length) {b : Nat} {ps fp : List Reg}
    (hps : ps.length = (ext.sig.returns.map retClass).length)
    (hps0 : retRegsC (ext.sig.returns.map retClass) 0 0 = some ps)
    (htr : ctx.tryRegs.1 = (ext.sig.returns.map retClass).zipIdx.map fun q => Reg.vreg (b + q.2) q.1)
    (hdefs : ∀ d ∈ (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
      List.replicate fp.length .int)).map (·.2.1), ∃ c, Reg.vreg d c ∈ tryDefRegs ctx)
    {st st' : LState} (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + 1) :
    LowerTryOkPC Rd Pc isem MR env cp ctx (.call fn args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
       [.loadExtNameGot (.vreg st.nextVreg .int) ext.name,
        .call ⟨.reg (.vreg st.nextVreg .int),
          argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))),
          callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
            List.replicate fp.length .int))⟩]) := by
  refine ⟨by omega, ⟨(stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
    [.loadExtNameGot (.vreg st.nextVreg .int) ext.name], _, by rw [List.append_assoc]; rfl, ?_,
    fun d hd => ?_⟩, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStoreC] at hd
    · simp only [List.mem_singleton] at hm
      subst hm
      rw [vdefs_got_ctl] at hd
      simp only [List.mem_singleton] at hd
      omega
  · rw [vdefs_call_regC] at hd
    exact hdefs d hd
  · intro fr cm ρ w hfr hvh hdfg hmr _ hpin
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
      obtain ⟨w1, hrun1, hmr1, hargsAt⟩ := argsAt_after_storesC hMR hMem hFP hout hso hb hl hty
        hlen.symm (valClassOf ctx) (fun j v x hv hx => hvh x v (hvx j x v hx hv))
        (argClasses_of_frame_sig hdfg hvals hty hso.2) hmr
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
      have hdl : (callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int))).length = ext.sig.returns.length + fp.length := by
        rw [callDefsC, List.length_map, outDefsC_app_length b hps, List.length_map]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w2
        (.reg (.vreg t .int)) (argPairsC (liftC (valClassOf ctx) (regPairsOf ((locs.zip args).zip bytes))))
        (callDefsC (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int))) info
        (upd ρ t (ofX (sym ext.name)) t ::
          (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg
        (.inr ⟨_, rfl, hcol, by rw [ht1, huses],
          siteRegsR_tryC hl hb (args_length_of hlen hty) _ hps0 _ _⟩) (by rw [hdl]; omega) hrets
        (hargsAt w2 hsw) hmr2 hpc hgo hrN
      rw [← liftC_vals (valClassOf ctx)] at hi
      have hol' : outs.length = (outDefsC b (ps ++ fp) (ext.sig.returns.map retClass ++
          List.replicate fp.length .int)).length := by
        rw [hol, callDefsC, List.length_map]
      have hrun3 := seqRun_tryCall_regC (info := info) hi hol'
      rw [show ∀ c : CallInfo, tryFix info ((stackEnts ((locs.zip args).zip bytes)).map
          (argStoreC (valClassOf ctx)) ++ [MInst.loadExtNameGot (.vreg t .int) ext.name, MInst.call c]) =
          ((stackEnts ((locs.zip args).zip bytes)).map (argStoreC (valClassOf ctx)) ++
            [MInst.loadExtNameGot (.vreg t .int) ext.name]) ++ [MInst.tryCall c info]
        from fun c => by rw [← tryFix_append info _ c]; simp]
      refine ⟨?_, _, _, _, _, _, outs, w',
        seqRun_append_fall_stop isem (seqRun_append_fall' isem hrun1 hrun2) hrun3, by simp,
        fun j r v hr hv => ?_, hmr'⟩
      · intro mi hmi u hu
        rcases List.mem_append.mp hmi with hmi | hmi
        · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hmi
          rw [vuseNums_argStoreC, List.mem_singleton] at hu
          subst hu
          exact .inr (usesOk_args hvals _ (map_zip_args (mem_args_of_stackEnts he)))
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmi
          rcases hmi with rfl | rfl
          · simp [vuseNums_got_ctl] at hu
          · rw [vuseNums_call_regC, liftC_fst] at hu
            rcases List.mem_cons.mp hu with rfl | hu
            · exact .inl (by omega)
            · exact .inr (usesOk_args hvals u (map_zip_args (mem_args_of_regPairs hu)))
      · obtain ⟨c, hc, rfl⟩ := tryRetsC_get htr hr
        refine ⟨b + j, c, rfl, ?_⟩
        rw [vdefUpd_call_regC]
        exact retsHeld_tryC hps (by rw [hol, hdl, List.length_map]) hro hv hc
    · trivial

/-! ## The rules -/

set_option maxHeartbeats 5000000 in
/-- **`bl`** (`rule_lower_2508`) over float-capable contexts, any extern signature. -/
theorem call_bl_ruleOkTFPR {p : Program} (hp : Data p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) :
    CallRuleOkTFP Rd Pc isem MR env cp exts outB p rule_lower_2508 := by
  intro f ctx hctx hexts ii info inst hi hcl hstk cfg hc m n st tr env' s1 out st' tr' hm hn
    hvb _ hmatch heval
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
  have hres := call_results_lengthC hctx hi hcl hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2508] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_typed, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, regsClasses_outRegsC,
    outRegsC_length,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, regsClasses_outRegsC, outRegsC_single,
    outRegsC_length, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegC hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_genC _ _ _ (valClassOf ctx) hb hl,
    ctor_gen_call_info_gen _ _ _ _ _ _ _ hl,
    mapM_single_map, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hps := retRegsC_lengthC _ _ _ ‹retRegsC _ 0 0 = some _›
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_call] at hmi
  cases hmi
  rw [callDefsC_outDefsC] at hs2
  refine ⟨_, ?_, _, rfl, call_sym_lowerInstOkTFPR hMR hMem hFP hout hCR hctx.func hext
    (hexts fn _ hext) (hstk fn args _ rfl hext) hb hl hps hres
    (by rw [hs2, hs1]; simp [LState.emit, freshC_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshC_emitted]

set_option maxHeartbeats 5000000 in
/-- **GOT + `blr`** (`rule_lower_2518`) over float-capable contexts, any extern signature. -/
theorem call_got_ruleOkTFPR {p : Program} (hp : Data p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) :
    CallRuleOkTFP Rd Pc isem MR env cp exts outB p rule_lower_2518 := by
  intro f ctx hctx hexts ii info inst hi hcl hstk cfg hc m n st tr env' s1 out st' tr' hm hn
    hvb hfirst hmatch heval
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
  have hres := call_results_lengthC hctx hi hcl hext
  simp only [ext_value_list_slice_iff, ext_func_ref_data_iff, hfn] at *
  isel_destruct; subst_vars
  simp only [List.cons.injEq, Option.some.injEq, and_true] at *
  isel_destruct; subst_vars
  isel_inv_simp [*, rule_lower_2518] at heval
  isel_destruct; subst_vars
  simp only [ctor_abi_sig_iff, ctor_gen_call_output_typed, ctor_put_in_regs_vec_iff,
    ctor_gen_call_rets_iff, ctor_try_call_none_iff, ctor_output_vec_iff, ctor_box_external_name_iff,
    regsClasses_outRegsC, outRegsC_length,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, Array.size_replicate] at *
  isel_destruct; subst_vars
  simp only [show (4:Nat) < 10 from by decide, ite_true] at *
  subst_vars
  simp only [ctor_output_vec_iff, ctor_gen_call_rets_iff, regsClasses_outRegsC, outRegsC_single,
    outRegsC_length, Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hbelow := mapM_valueReg_below hvb ‹List.mapM ctx.valueReg? args = some _›
  have hrs := mapM_valueRegC hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_genC _ _ _ (valClassOf ctx) hb hl, mapM_single_map,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  have h570 := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  obtain ⟨rfl, hs0⟩ := kL _ (by omega) _ _ _ _ _ h570
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true,
    ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hps := retRegsC_lengthC _ _ _ ‹retRegsC _ 0 0 = some _›
  simp only [ctor_output_vec_iff] at *
  isel_destruct; subst_vars
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  have hfr : ∀ (cs : List RegClass) (e : Array MInst),
      (({ freshC st cs with emitted := e } : LState).fresh .int).1 =
      .vreg (st.nextVreg + cs.length) .int := fun cs e => by
    simp [LState.fresh, freshC_nextVreg]
  rw [hfr, callDefsC_outDefsC] at hs2
  rw [hfr] at hs0
  refine ⟨_, ?_, _, rfl, call_got_lowerInstOkTFPR hMR hMem hFP hout hCR hctx.func hext
    (hexts fn _ hext) hcol (hstk fn args _ rfl hext) hb hl hps (by assumption) hres hbelow
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh, freshC_nextVreg])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh, freshC_emitted]
  rw [← Array.toList_inj]
  simp

set_option maxHeartbeats 5000000 in
/-- **`try_call` by `bl`** (`rule_lower_2542`) over float-capable contexts, any extern signature. -/
theorem try_bl_ruleOkTFPR {p : Program} (hp : Data p) (hpT : TryData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) :
    TryRuleOkTFP Rd Pc isem MR env cp exts outB p rule_lower_2542 := by
  intro f ctx hctx hexts ti fn args et data sig items targets info lo st1 hreg hd he hi hinfo
    htr hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst _ hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallDataC_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallDataC_eq he hext hsig] at hd
  cases hd
  subst hsig
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  obtain ⟨ps0, hps0, htr1, hD, -⟩ := tryRegsOfC_defs htr
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  ctl_inv [*, rule_lower_2542, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iffC] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iffC, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff] at * <;>
    isel_destruct <;> subst_vars)
  have hx' := ‹ctx.func.extern? fn = some _›
  rw [hctx.func, hext] at hx'
  cases hx'
  have hti' := ‹tryInfoOf ext.sig items targets = some _›
  rw [hinfo] at hti'
  cases hti'
  obtain ⟨bytes, hb⟩ := ctor_gen_call_args_bytes ‹externCtor ctx T.gen_call_args _ _ = _›
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegC hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_genC _ _ _ (valClassOf ctx) hb hl, mapM_single_map,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  try (simp only [ctor_gen_try_call_rets_iffC] at *; isel_destruct; subst_vars)
  simp only [ctor_gen_call_info_gen _ _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hps := retRegsC_lengthC _ _ _ hps0
  have h638 := ‹ApplyInternal _ _ _ _ 46 638 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h638
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_call] at hmi
  cases hmi
  have hpsq := ‹retRegsC _ 0 0 = some _›
  rw [hps0] at hpsq
  cases hpsq
  rw [hD] at hs2
  simp only at hs1 hs2
  refine ⟨_, ?_, try_sym_lowerTryOkTFPR hMR hMem hFP hout hCR hctx.func hext (hexts fn _ hext)
    (hreg _ hext) hb hl (Nat.le_of_eq (tryInfoOf_rets hinfo)) hps htr1
    (tryDefsC_mem hD) (by rw [hs2, hs1]; simp [LState.emit])⟩
  rw [hs2, hs1]; simp [LState.emit]

set_option maxHeartbeats 20000000 in
/-- **`try_call` by GOT + `blr`** (`rule_lower_2551`) over float-capable contexts, any extern
signature. -/
theorem try_got_ruleOkTFPR {p : Program} (hp : Data p) (hpT : TryData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) (hFP : MemRefinesFP Rd F sb isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) :
    TryRuleOkTFP Rd Pc isem MR env cp exts outB p rule_lower_2551 := by
  intro f ctx hctx hexts ti fn args et data sig items targets info lo st1 hreg hd he hi hinfo
    htr hvb cfg hc m n st tr env' s1 out st' tr' hm hn hst hfirst hmatch heval
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 100 := ⟨m - 100, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n', n = n' + 100 := ⟨n - 100, by omega⟩
  have kC := fun n (hn : 30 ≤ n) i s v s' h => call_ind_impl_ok hp (ctx := ctx) hc (n := n) (i := i)
    (s := s) (v := v) (s' := s') hn h
  have kE := fun n (hn : 30 ≤ n) i s v s' h => emit_side_effect_inst_ok hp (ctx := ctx) hc (n := n)
    (i := i) (s := s) (v := v) (s' := s') hn h
  have kL := fun n (hn : 40 ≤ n) nm d s v s' h => load_ext_name_ok_ctl hp (ctx := ctx) hc (n := n)
    (nm := nm) (d := d) (s := s) (v := v) (s' := s') hn h
  obtain ⟨sig0, items0, ext, he0, hext, hsig⟩ := tryCallDataC_spec hd
  rw [he] at he0
  simp only [Except.ok.injEq, Prod.mk.injEq] at he0
  obtain ⟨rfl, rfl⟩ := he0
  rw [tryCallDataC_eq he hext hsig] at hd
  cases hd
  subst hsig
  have hfn : ctx.func.extern? fn = some ext := by rw [hctx.func]; exact hext
  have hcol : ext.colocated = false := try_got_not_colocated hp hpT hi hfirst hfn
  clear hfirst
  obtain ⟨ps0, hps0, htr1, hD, hst1⟩ := tryRegsOfC_defs htr
  cases hp
  obtain ⟨t300, t302, t2297, t2474⟩ := hpT
  ctl_inv [*, rule_lower_2551, ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iffC, ctor_box_external_name_iff] at hmatch heval
  simp only [hi, hfn, Option.some.injEq] at *
  isel_destruct; subst_vars
  repeat (isel_inv_simp [ext_func_ref_data_iff, ctor_abi_sig_iff, ctor_try_call_info_iff,
    ctor_gen_try_call_rets_iffC, ext_value_list_slice_iff, ctor_put_in_regs_vec_iff,
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
  have hrs := mapM_valueRegC hctx ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  simp only [ctor_gen_call_args_genC _ _ _ (valClassOf ctx) hb hl, mapM_single_map,
    Option.some.injEq, exists_eq_left'] at *
  isel_destruct; subst_vars
  have h570 := ‹ApplyInternal _ _ _ _ 27 570 _ _ _ _›
  obtain ⟨rfl, hs0⟩ := kL _ (by omega) _ _ _ _ _ h570
  try (simp only [ctor_gen_try_call_rets_iffC] at *; isel_destruct; subst_vars)
  simp only [ctor_gen_call_ind_info_gen _ _ _ _ _ _ hl, Nat.reduceEqDiff, Nat.reduceLT,
    ite_true, ite_false, Option.some.injEq] at *
  isel_destruct; subst_vars
  have hps := retRegsC_lengthC _ _ _ hps0
  have h639 := ‹ApplyInternal _ _ _ _ 46 639 _ _ _ _›
  obtain ⟨hs1, rfl⟩ := kC _ (by omega) _ _ _ _ h639
  have h242 := ‹ApplyInternal _ _ _ _ 13 242 _ _ _ _›
  obtain ⟨mi, hmi, hs2, -⟩ := kE _ (by omega) _ _ _ _ h242
  rw [ofV_callInd] at hmi
  cases hmi
  have hpsq := ‹retRegsC _ 0 0 = some _›
  rw [hps0] at hpsq
  cases hpsq
  rw [hD] at hs2
  rw [show ∀ s : LState, (s.fresh .int).1 = .vreg s.nextVreg .int from fun s => rfl] at hs2 hs0
  simp only at hs0 hs1 hs2
  refine ⟨_, ?_, try_got_lowerTryOkTFPR hMR hMem hFP hout hCR hctx.func hext (hexts fn _ hext) hcol
    (hreg _ hext) hb hl (Nat.le_of_eq (tryInfoOf_rets hinfo)) hps (by assumption) htr1 (tryDefsC_mem hD)
    (fun x hx => by have := hbelow x hx; omega)
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh]
  rw [← Array.toList_inj]
  simp

/-! ## Assembly -/

set_option maxRecDepth 100000 in
/-- **`CallRulesCorrectTFPR`**: under the callee contract with registers and the guarded integer and float
memory forms, the `call` rules of `lower` (1031, 1032) are correct over float-capable contexts,
for calls of any extern signature (`f32`/`f64` arguments in v0..v7 or on the stack, `f32`/`f64`
returns from v0..v7). -/
theorem callRulesCorrectTFPR_program : CallRulesCorrectTFPR program := by
  intro Rd Pc F isem MR env cp exts sb syms outB _ hMR hMem hFP hout hCR r hr hroot
  simp only [callRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  rcases hroot with h | h
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2508 (by rw [h]; rfl)]
    exact call_bl_ruleOkTFPR data_program hMR hMem hFP hout hCR
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2518 (by rw [h]; rfl)]
    exact call_got_ruleOkTFPR data_program hMR hMem hFP hout hCR

set_option maxRecDepth 100000 in
/-- **`TryRulesCorrectTFPR`**: under the callee contract with registers and the guarded integer and float
memory forms, the `try_call` rules of `lower_branch` (1034, 1035) are correct over float-capable
contexts, for `try_call`s of any extern signature (`f32`/`f64` arguments in v0..v7 or on the
stack, `f32`/`f64` returns from v0..v7 into fresh float vregs). -/
theorem tryRulesCorrectTFPR_program : TryRulesCorrectTFPR program := by
  intro Rd Pc F isem MR env cp exts sb syms outB _ hMR hMem hFP hout hCR r hr hroot
  simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  rcases hroot with h | h
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2542 (by rw [h]; rfl)]
    exact try_bl_ruleOkTFPR data_program tryData_program hMR hMem hFP hout hCR
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2551 (by rw [h]; rfl)]
    exact try_got_ruleOkTFPR data_program tryData_program hMR hMem hFP hout hCR

end Backend.Proof
