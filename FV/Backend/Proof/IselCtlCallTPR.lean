import FV.Backend.Proof.IselContractPR
import FV.Backend.Proof.IselCtlTryTI

/-!
# The call rules with the call site's registers (#753, stage R1): typed contexts

The rule theorems of `IselCtlCallTI` and `IselCtlTryTI` (`CtxT` contexts) under the contracts with
registers (`CallsRefinePR`, `IndCallsRefinePR`, `IselContractPR`), as `IselCtlCallPR` does for the
integer ones: `call_got_lowerInstOkTPR`, `call_ind_lowerInstOkTPR`, `try_got_lowerTryOkTPR`,
`try_ind_lowerTryOkTPR` (and `call_sym_lowerInstOkTPR`, `try_sym_lowerTryOkTPR`); the rules
`…_ruleOkTPR`; the families `callRulesCorrectTPR_program`, `indRulesCorrectTPR_program`,
`tryRulesCorrectTPR_program`, `tryIndRulesCorrectTPR_program`.
-/

namespace Backend.Proof

open Backend Isle Isle.Interp Isle.Aarch64

set_option maxRecDepth 20000
set_option autoImplicit false

/-! ## The lowering of the call sites -/

theorem call_sym_lowerInstOkTPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc} (hCR : CallsRefinePR Pc F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx}
    (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S))
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hst' : st'.nextVreg = st.nextVreg + ext.sig.returns.length) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.call fn args) results st
      (outRegs' st.nextVreg ext.sig.returns.length) st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
        [.call ⟨.sym ext.name, retPairs (regPairsOf ((locs.zip args).zip bytes)),
          callDefs (outDefs st.nextVreg ext.sig.returns.length)⟩]) := by
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
      have hdl : (callDefs (outDefs st.nextVreg ext.sig.returns.length)).length =
          ext.sig.returns.length := by simp [callDefs, outDefs]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w1 (.sym ext.name)
        (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs st.nextVreg ext.sig.returns.length))
        _ _ vals rvals cm' hg (.inl ⟨rfl, rfl⟩) hdl (hargs w1 (SameWorldNF.refl F w1)) hmr1 hpc hgo
        hrN
      have hol' : outs.length = (outDefs st.nextVreg ext.sig.returns.length).length := by
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

theorem call_got_lowerInstOkTPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc} (hCR : CallsRefinePR Pc F env exts MR isem)
    {f : Clif.Function}
    {ctx : Ctx} (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hcol : ext.colocated = false)
    (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S))
    (hrc : (sigRets ext.sig).map retClass = List.replicate (sigRets ext.sig).length .int)
    {st st' : LState} {results : List Nat} (hres : results.length = ext.sig.returns.length)
    (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + ext.sig.returns.length + 1) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.call fn args) results st
      (outRegs' st.nextVreg ext.sig.returns.length) st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
       [.loadExtNameGot (.vreg (st.nextVreg + ext.sig.returns.length) .int) ext.name,
       .call ⟨.reg (.vreg (st.nextVreg + ext.sig.returns.length) .int),
        retPairs (regPairsOf ((locs.zip args).zip bytes)),
        callDefs (outDefs st.nextVreg ext.sig.returns.length)⟩]) := by
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
      have hdl : (callDefs (outDefs st.nextVreg ext.sig.returns.length)).length =
          ext.sig.returns.length := by simp [callDefs, outDefs]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall ext hin g fr.slots cm w2
        (.reg (.vreg t .int)) (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs st.nextVreg ext.sig.returns.length))
        (upd ρ t (ofX (sym ext.name)) t ::
          (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg
        (.inr ⟨_, rfl, hcol, by rw [ht1, huses],
          siteRegsR_int hl hb (args_length_of hlen hty) (returns_retClass_of_sigRets hrc) _
            (Nat.le_refl _)⟩) hdl (hargsAt w2 hsw) hmr2 hpc hgo hrN
      have hol' : outs.length = (outDefs st.nextVreg ext.sig.returns.length).length := by
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

theorem call_ind_lowerInstOkTPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {sigs : List Clif.Signature}
    (hCR : IndCallsRefinePR Pc env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hfunc : ctx.func = f) {sig callee : Nat} {args : List Nat}
    {s : Clif.Signature} (hs : f.sigDecls.lookup sig = some s) (hin : s ∈ sigs)
    (hso : SigStackOk s outB) {bytes : List Nat} (hb : sigParamBytes s = .ok bytes)
    {locs : List ArgLoc} {S : Nat} (hl : sigArgLocs s = .ok (locs, S))
    (hrc : (sigRets s).map retClass = List.replicate (sigRets s).length .int)
    {st st' : LState} {results : List Nat}
    (hres : results.length = s.returns.length)
    (hst' : st'.nextVreg = st.nextVreg + s.returns.length) :
    LowerInstOkP Rd Pc isem MR env cp ctx (.callIndirect sig callee args) results st
      (outRegs' st.nextVreg s.returns.length) st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
        [.call ⟨.reg (.vreg callee .int), retPairs (regPairsOf ((locs.zip args).zip bytes)),
          callDefs (outDefs st.nextVreg s.returns.length)⟩]) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro m hm d hd
    rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨e, -, rfl⟩ := List.mem_map.mp hm
      simp [vdefs_argStore] at hd
    · simp only [List.mem_singleton] at hm
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
      have hrN : rvals.length = s.returns.length := by
        have := congrArg List.length hrty; simpa [Clif.AbiParam.tys] using this
      obtain ⟨hlen, hvx⟩ := getMany_ok hvals
      obtain ⟨w1, hrun1, hmr1, hargsAt⟩ := argsAt_after_stores hMR hMem hout hso hb hl hty
        hlen.symm (fun j v x hv hx => hvh x v (hvx j x v hx hv)) hmr
      have hdl : (callDefs (outDefs st.nextVreg s.returns.length)).length =
          s.returns.length := by
        simp [callDefs, outDefs]
      have hlo : lo64 (ρ callee) = BitVec.ofNat 64 x.toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact lo64_of_vholds (hvh callee _ (frame_get_regs hcv))
      obtain ⟨hcall, -⟩ := hCR
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := hcall s hin name g fr.slots cm w1 x.toNat
        (.vreg callee .int) (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs st.nextVreg s.returns.length)) (ρ callee)
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm'
        hg hsg hsym hlo hdl (hargsAt w1 (SameWorldNF.refl F w1)) hmr1 hpc hgo hrN hty
        (siteRegsR_int hl hb (args_length_of hlen hty) (returns_retClass_of_sigRets hrc) _
            (Nat.le_refl _))
      have hol' : outs.length = (outDefs st.nextVreg s.returns.length).length := by
        rw [hol]; simp [callDefs, outDefs]
      refine ⟨?_, _, _, seqRun_append_fall' isem hrun1 (seqRun_call_reg hi hol'),
        results_call hrN hres (by rw [hol, hdl]) hro, hmr'⟩
      intro mi hmi u hu
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
    · intro h; simp [explicitTrapInst] at h
    · trivial

theorem try_sym_lowerTryOkTPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc} (hCR : CallsRefinePR Pc F env exts MR isem)
    {f : Clif.Function} {ctx : Ctx} (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat}
    {ext : Clif.ExtFunc} (hext : f.extern? fn = some ext) (hin : ext ∈ exts)
    (hso : SigStackOk ext.sig outB) {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes)
    {locs : List ArgLoc} {S : Nat} (hl : sigArgLocs ext.sig = .ok (locs, S)) {info : TryInfo}
    (hrets : info.rets ≤ ext.sig.returns.length) {b : Nat}
    (htr : ctx.tryRegs = ((List.range ext.sig.returns.length).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int]))
    {st st' : LState} (hst' : st'.nextVreg = st.nextVreg) :
    LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
        [.call ⟨.sym ext.name, retPairs (regPairsOf ((locs.zip args).zip bytes)),
          callDefs (outDefs b (max ext.sig.returns.length 2))⟩]) := by
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
      have hdl : (callDefs (outDefs b (max ext.sig.returns.length 2))).length =
          max ext.sig.returns.length 2 := by
        simp [callDefs, outDefs]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w1 (.sym ext.name)
        (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs b (max ext.sig.returns.length 2))) info
        _ _ vals rvals cm' hg (.inl ⟨rfl, rfl⟩) (by rw [hdl]; exact Nat.le_max_left _ _) hrets
        (hargsAt w1 (SameWorldNF.refl F w1)) hmr1 hpc hgo hrN
      have hol' : outs.length = (outDefs b (max ext.sig.returns.length 2)).length := by
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

theorem try_got_lowerTryOkTPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc} (hCR : CallsRefinePR Pc F env exts MR isem)
    {f : Clif.Function}
    {ctx : Ctx} (hfunc : ctx.func = f) {fn : Clif.FnRef} {args : List Nat} {ext : Clif.ExtFunc}
    (hext : f.extern? fn = some ext) (hin : ext ∈ exts) (hcol : ext.colocated = false)
    (hso : SigStackOk ext.sig outB)
    {bytes : List Nat} (hb : sigParamBytes ext.sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs ext.sig = .ok (locs, S))
    (hsE : sigIntB ext.sig = true) {info : TryInfo}
    (hrets : info.rets ≤ ext.sig.returns.length) {b : Nat}
    (htr : ctx.tryRegs = ((List.range ext.sig.returns.length).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int]))
    {st st' : LState} (hargs : ∀ x ∈ args, x < st.nextVreg)
    (hst' : st'.nextVreg = st.nextVreg + 1) :
    LowerTryOkP Rd Pc isem MR env cp ctx (.call fn args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
       [.loadExtNameGot (.vreg st.nextVreg .int) ext.name,
       .call ⟨.reg (.vreg st.nextVreg .int),
        retPairs (regPairsOf ((locs.zip args).zip bytes)),
        callDefs (outDefs b (max ext.sig.returns.length 2))⟩]) := by
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
      have hdl : (callDefs (outDefs b (max ext.sig.returns.length 2))).length =
          max ext.sig.returns.length 2 := by
        simp [callDefs, outDefs]
      have ht1 : upd ρ t (ofX (sym ext.name)) t = ofX (sym ext.name) := by simp [upd]
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry ext hin g fr.slots cm w2
        (.reg (.vreg t .int)) (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs b (max ext.sig.returns.length 2))) info
        (upd ρ t (ofX (sym ext.name)) t ::
          (regPairsOf ((locs.zip args).zip bytes)).map (upd ρ t (ofX (sym ext.name)) ·.1))
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg
        (.inr ⟨_, rfl, hcol, by rw [ht1, huses],
          siteRegsR_int hl hb (args_length_of hlen hty) (returns_retClass_of_sigIntB hsE) _
            (Nat.le_max_left _ _)⟩) (by rw [hdl]; exact Nat.le_max_left _ _) hrets
        (hargsAt w2 hsw) hmr2 hpc hgo hrN
      have hol' : outs.length = (outDefs b (max ext.sig.returns.length 2)).length := by
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

theorem try_ind_lowerTryOkTPR {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} {sb : Nat} {syms : String → Option Nat}
    (hMR : MRStable F MR) (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR)
    {sigs : List Clif.Signature} (hCR : IndCallsRefinePR Pc env sigs MR isem)
    {f : Clif.Function} {ctx : Ctx} (hfunc : ctx.func = f) {callee : Nat} {args : List Nat}
    {et : Clif.ExnTable} {sig : Clif.Signature} (hsd : f.sigDecls.lookup et.sig = some sig)
    (hin : sig ∈ sigs) (hso : SigStackOk sig outB) {bytes : List Nat}
    (hb : sigParamBytes sig = .ok bytes) {locs : List ArgLoc} {S : Nat}
    (hl : sigArgLocs sig = .ok (locs, S))
    (hsI : sigIntB sig = true) {info : TryInfo}
    (hrets : info.rets ≤ sig.returns.length) {b : Nat}
    (htr : ctx.tryRegs = ((List.range sig.returns.length).map fun j => Reg.vreg (b + j) .int,
      [.vreg b .int, .vreg (b + 1) .int]))
    {st st' : LState} (hst' : st'.nextVreg = st.nextVreg) :
    LowerTryOkP Rd Pc isem MR env cp ctx (.callIndirect et.sig callee args) info st st'
      ((stackEnts ((locs.zip args).zip bytes)).map argStore ++
        [.call ⟨.reg (.vreg callee .int), retPairs (regPairsOf ((locs.zip args).zip bytes)),
          callDefs (outDefs b (max sig.returns.length 2))⟩]) := by
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
      have hdl : (callDefs (outDefs b (max sig.returns.length 2))).length =
          max sig.returns.length 2 := by
        simp [callDefs, outDefs]
      have hlo : lo64 (ρ callee) = BitVec.ofNat 64 x.toNat := by
        rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
        exact lo64_of_vholds (hvh callee _ (frame_get_regs hcv))
      obtain ⟨-, htry⟩ := hCR
      obtain ⟨outs, w', hi, hol, hro, hmr'⟩ := htry sig hin name g fr.slots cm w1 x.toNat
        (.vreg callee .int) (retPairs (regPairsOf ((locs.zip args).zip bytes)))
        (callDefs (outDefs b (max sig.returns.length 2))) info (ρ callee)
        ((regPairsOf ((locs.zip args).zip bytes)).map (ρ ·.1)) vals rvals cm' hg hsg hsym hlo
        (by rw [hdl]; exact Nat.le_max_left _ _) hrets (hargsAt w1 (SameWorldNF.refl F w1)) hmr1
        hpc hgo hrN hty
        (siteRegsR_int hl hb (args_length_of hlen hty) (returns_retClass_of_sigIntB hsI) _
            (Nat.le_max_left _ _))
      have hol' : outs.length = (outDefs b (max sig.returns.length 2)).length := by
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

/-! ## The rules -/

set_option maxHeartbeats 5000000 in
/-- **`bl`** (`rule_lower_2508`) over typed contexts. -/
theorem call_bl_ruleOkTPR {p : Program} (hp : Data p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) :
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
  have hops : ∀ x ∈ args, IntPos ctx x := fun x hx => hctxT.callArgs ii info fn args hi hcl x hx
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
  refine ⟨_, ?_, _, rfl, call_sym_lowerInstOkTPR hMR hMem hout hCR hctx.func hext (hexts fn _ hext)
    (hstk fn args _ rfl hext) hb hl hres (by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshN_emitted]

set_option maxHeartbeats 5000000 in
/-- **GOT + `blr`** (`rule_lower_2518`) over typed contexts. -/
theorem call_got_ruleOkTPR {p : Program} (hp : Data p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) :
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
  have hops : ∀ x ∈ args, IntPos ctx x := fun x hx => hctxT.callArgs ii info fn args hi hcl x hx
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
  refine ⟨_, ?_, _, rfl, call_got_lowerInstOkTPR hMR hMem hout hCR hctx.func hext (hexts fn _ hext)
    hcol (hstk fn args _ rfl hext) hb hl (by assumption) hres hbelow
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh, freshN_nextVreg])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh, freshN_emitted]
  rw [← Array.toList_inj]
  simp

set_option maxHeartbeats 5000000 in
/-- **`blr` of the callee value** (`rule_lower_2529`, `call_indirect`) over typed contexts. -/
theorem call_ind_ruleOkTPR {p : Program} (hp : Data p) (hpI : IndData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat} (hout : OutArgsOk F outB MR)
    {sigs : List Clif.Signature} (hIstk : IndStack sigs outB)
    (hCR : IndCallsRefinePR Pc env sigs MR isem) :
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
  have hin := hsig sig callee args s rfl hs
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
  obtain ⟨locs, S, hl⟩ := ctor_gen_call_args_locs ‹externCtor ctx T.gen_call_args _ _ = _›
  have hrs := mapM_valueRegTI hctx (fun x hx => hops x (List.mem_cons_of_mem _ hx))
    ‹List.mapM ctx.valueReg? args = some _›
  subst hrs
  have htgt := hctx.valueReg_int ‹ctx.valueReg? callee = some _› (hops callee List.mem_cons_self)
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
  rw [callDefs_outDefs] at hs2
  rw [outRegs_eq]
  refine ⟨_, ?_, _, rfl, call_ind_lowerInstOkTPR hMR hMem hout hCR hctx.func hs hin (hIstk s hin)
    hb hl (by assumption) hres
    (by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshN_emitted]

set_option maxHeartbeats 5000000 in
/-- **`try_call` by `bl`** (`rule_lower_2542`) over typed contexts. -/
theorem try_bl_ruleOkTPR {p : Program} (hp : Data p) (hpT : TryData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem}
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) :
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
  have hcd : ((List.range (max ext.sig.returns.length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max ext.sig.returns.length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine ⟨_, ?_, try_sym_lowerTryOkTPR hMR hMem hout hCR hctx.func hext (hexts fn _ hext)
    (hreg _ hext) hb hl (Nat.le_of_eq (tryInfoOf_rets hinfo)) htrs
    (by rw [hs2, hs1]; simp [LState.emit, freshN_nextVreg])⟩
  rw [hs2, hs1]; simp [LState.emit, freshN_emitted]

set_option maxHeartbeats 20000000 in
/-- **`try_call` by GOT + `blr`** (`rule_lower_2551`) over typed contexts. -/
theorem try_got_ruleOkTPR {p : Program} (hp : Data p) (hpT : TryData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop}
    {isem : Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} (hR : Refines F isem)
    (hMR : MRStable F MR) {sb : Nat} {syms : String → Option Nat}
    (hMem : MemRefinesR Rd F sb syms isem)
    {outB : Nat} (hout : OutArgsOk F outB MR) {exts : List Clif.ExtFunc}
    (hCR : CallsRefinePR Pc F env exts MR isem) :
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
  have hcd : ((List.range (max ext.sig.returns.length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max ext.sig.returns.length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs0 hs1 hs2
  refine ⟨_, ?_, try_got_lowerTryOkTPR hMR hMem hout hCR hctx.func hext (hexts fn _ hext) hcol
    (hreg _ hext) hb hl (by assumption) (Nat.le_of_eq (tryInfoOf_rets hinfo)) htrs
    (fun x hx => by have := hbelow x hx; omega)
    (by rw [hs2, hs1, hs0]; simp [LState.emit, LState.fresh])⟩
  rw [hs2, hs1, hs0]
  simp only [LState.emit, LState.fresh]
  rw [← Array.toList_inj]
  simp

set_option maxHeartbeats 20000000 in
/-- **`try_call_indirect`** (`rule_lower_2561`) over typed contexts. -/
theorem try_ind_ruleOkTPR {p : Program} (hp : Data p) (hpT : TryData p) (hpI : IndData p)
    (hpJ : TryIndData p) {Rd F : BitVec 64 → Prop}
    {Pc : String → Clif.Signature → List Clif.Val → Clif.Mem → Prop} {isem : Sem} {MR : MemRelT}
    {env : Clif.Env}
    {cp : Clif.Program} (hR : Refines F isem) (hMR : MRStable F MR) {sb : Nat}
    {syms : String → Option Nat} (hMem : MemRefinesR Rd F sb syms isem) {outB : Nat}
    (hout : OutArgsOk F outB MR) {sigs : List Clif.Signature} (hIstk : IndStack sigs outB)
    (hCR : IndCallsRefinePR Pc env sigs MR isem) :
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
  have hcd : ((List.range (max sig.returns.length 2)).map fun j =>
      (Reg.x j, Reg.vreg (lo.nextVreg + j) .int)) =
      callDefs (outDefs lo.nextVreg (max sig.returns.length 2)) := by
    simp [callDefs, outDefs, List.map_map, Function.comp_def]
  rw [hcd] at hs2
  simp only at hs1 hs2
  refine ⟨_, ?_, try_ind_lowerTryOkTPR hMR hMem hout hCR hctx.func (exnTableOpnd_sig he) hsig
    (hIstk sig hsig) hb hl (by assumption) (Nat.le_of_eq (tryInfoOf_rets hinfo)) htrs
    (by rw [hs2, hs1]; simp [LState.emit])⟩
  rw [hs2, hs1]; simp [LState.emit]

/-! ## Assembly -/

set_option maxRecDepth 100000 in
/-- **`CallRulesCorrectTPR`**: under the callee contract with registers and the guarded memory forms, the
`call` rules of `lower` (1031, 1032) are correct over typed contexts. -/
theorem callRulesCorrectTPR_program : CallRulesCorrectTPR program := by
  intro Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR r hr hroot
  simp only [callRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  rcases hroot with h | h
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2508 (by rw [h]; rfl)]
    exact call_bl_ruleOkTPR data_program hR hMR hMem hout hCR
  · rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2518 (by rw [h]; rfl)]
    exact call_got_ruleOkTPR data_program hR hMR hMem hout hCR

set_option maxRecDepth 100000 in
/-- **`IndRulesCorrectTPR`**: under the indirect-call contract with registers, guarded memory forms and an
outgoing area holding the stack arguments (S5), the `call_indirect` rule of `lower` (1033) is
correct over typed contexts. -/
theorem indRulesCorrectTPR_program : IndRulesCorrectTPR program := by
  intro Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR r hr hroot
  simp only [indRootRule, beq_iff_eq] at hroot
  rw [eq_of_mem_of_id lower_ids_nodup hr mem_lower_2529 (by rw [hroot]; rfl)]
  exact call_ind_ruleOkTPR data_program indData_program hR hMR hMem hout hIstk hCR

set_option maxRecDepth 100000 in
/-- **`TryRulesCorrectTPR`**: under the callee contract with registers and the guarded memory forms, the
`try_call` rules of `lower_branch` (1034, 1035) are correct over typed contexts. -/
theorem tryRulesCorrectTPR_program : TryRulesCorrectTPR program := by
  intro Rd Pc F isem MR env cp exts sb syms outB hR hMR hMem hout hCR r hr hroot
  simp only [tryRootRule, Bool.or_eq_true, beq_iff_eq] at hroot
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  rcases hroot with h | h
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2542 (by rw [h]; rfl)]
    exact try_bl_ruleOkTPR data_program tryData_program hR hMR hMem hout hCR
  · rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2551 (by rw [h]; rfl)]
    exact try_got_ruleOkTPR data_program tryData_program hR hMR hMem hout hCR

set_option maxRecDepth 100000 in
/-- **`TryIndRulesCorrectTPR`**: under the indirect-call contract with registers, guarded memory forms and
an outgoing area holding the stack arguments (S5), the `try_call_indirect` rule of
`lower_branch` (1036) is correct over typed contexts. -/
theorem tryIndRulesCorrectTPR_program : TryIndRulesCorrectTPR program := by
  intro Rd Pc F isem MR env cp sigs sb syms outB hR hMR hMem hout hIstk hCR r hr hroot
  simp only [tryIndRootRule, beq_iff_eq] at hroot
  have hnd : ((program.rulesOf TId.lower_branch).map Rule.id).Nodup := by
    rw [show TId.lower_branch = 687 from rfl, data_program.r687]
    decide +kernel
  rw [eq_of_mem_of_rid hnd hr mem_lower_branch_2561 (by rw [hroot]; rfl)]
  exact try_ind_ruleOkTPR data_program tryData_program indData_program tryIndData_program hR hMR
    hMem hout hIstk hCR

end Backend.Proof
