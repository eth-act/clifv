import FV.Backend.Proof.IselCovTDriver
import FV.Backend.Proof.IselCovTFamCover
import FV.Backend.Proof.FormsCoverComplete
import FV.Backend.Proof.SpillEdgesT

/-!
# Form coverage without `formsCoveredB` on the typed scope (typed V3)

`formsCovered_completeT`: on input in `Dominated` and the typed scope `LowerScopeT` whose float
`store`s and `select`s are class-checked (`Compile.storeTypedB`, `Compile.selectTypedB`), every
instruction of `prepare`'s output of `lowerFunction`'s VCode is a control form or a covered
straight-line form (`FormsCovered`). The driver's ISLE runs are covered by the typed abstract
interpretation (`CovT.stmt_covT`, `CovT.termCall_covT`, `CovT.tryCall_covT`; the statements'
families `CovT.famCover_of`, the terminators' `CovT.termFam_of`), a statement's results are
vregs so the driver adds no result `mov` (`extraOfT_nil_of_vregs`), and the driver's own
instructions, its renaming and `prepare` keep coverage (`formsCovered_of_runsT`).
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Cov

theorem vcBlocksT_all' (P : MInst → Prop)
    (hR : ∀ R gn, VRenaming R gn → ∀ m, P m → P (m.mapRegs R))
    (hargs : ∀ ds, P (.args ds))
    (hload : ∀ n c b off, P (stackArgLoad (.vreg n c) b (.fpOffset off)))
    (hjump : ∀ l, P (.jump l))
    {f : Clif.Function} {ctx : Ctx} {bl : List BLow}
    (hs : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm →
      L.sl[j]? = some sl → ∀ m ∈ sl.st'.emitted.toList, P m)
    (hx : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm →
      L.sl[j]? = some sl → ∀ m ∈ extraOfT ctx stm.results sl.rss, P m)
    (ht : ∀ (bi : Nat) (B : Clif.Block) (L : BLow), f.blocks[bi]? = some B → bl[bi]? = some L →
      ∀ m ∈ fixTry L.tl L.tst'.emitted.toList, P m) :
    ∀ vb ∈ (vcBlocksOfT f ctx bl).toList, ∀ m ∈ vb.insts.toList, P m := by
  intro vb hvb m hm
  obtain ⟨R, ⟨gn, hRg⟩, ⟨bi, B, L, hB, hL, rfl⟩ | ⟨B, L, e, -, he, rfl⟩⟩ := mem_vcBlocksOfT hvb
  · simp only [fixBlock, rawBlockT, Array.toList_map, List.mem_map, List.mem_append,
      List.mem_flatten] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    apply hR R gn hRg
    rcases hm0 with (hpre | ⟨sg, hsg, hm0⟩) | htseg
    · unfold preT at hpre
      split at hpre
      · simp only [List.mem_cons] at hpre
        rcases hpre with rfl | hpre
        · exact hargs _
        · simp only [entryLoadsT, List.mem_filterMap] at hpre
          obtain ⟨q, -, hq⟩ := hpre
          unfold entryLoadOfT at hq
          split at hq
          · cases hq; exact hload _ _ _ _
          · cases hq
      · simp at hpre
    · simp only [List.mem_range] at hsg
      obtain ⟨j, -, rfl⟩ := hsg
      unfold segT at hm0
      rw [hB, hL] at hm0
      simp only at hm0
      split at hm0
      · rename_i stm sl hstm hsl
        simp only [List.mem_map] at hm0
        obtain ⟨m1, hm1, rfl⟩ := hm0
        refine hR id id vrenaming_id _ ?_
        rcases List.mem_append.mp hm1 with hm1 | hm1
        · exact hs bi B L j stm sl hB hL hstm hsl m1 hm1
        · exact hx bi B L j stm sl hB hL hstm hsl m1 hm1
      · simp at hm0
    · unfold tseg at htseg
      rw [hL] at htseg
      simp only [List.mem_map] at htseg
      obtain ⟨m1, hm1, rfl⟩ := htseg
      exact hR id id vrenaming_id _ (ht bi B L hB hL m1 hm1)
  · obtain ⟨tl, hi⟩ := edgeBlocksT_insts he
    simp only [fixBlock, hi, Array.toList_map, List.mem_map] at hm
    obtain ⟨m0, hm0, rfl⟩ := hm
    simp at hm0
    subst hm0
    exact hR R gn hRg _ (hjump tl)

/-- Renaming keeps the typed coverage `CovT.Covered`. -/
theorem coveredT_mapRegs {R : Reg → Reg} {gn : Nat → Nat} (hg : VRenaming R gn) (m : MInst) :
    CovT.Covered (m.mapRegs R) = CovT.Covered m := by
  unfold CovT.Covered
  rw [isCtl_mapRegs, formOk_mapRegs hg, isPoolLoad_mapRegs hg]

/-- The load of a stack-passed parameter into a vreg is covered. -/
theorem covered_stackArgLoad (n : Nat) (c : RegClass) (b : Nat) (off : Int) :
    Cov.Covered (stackArgLoad (.vreg n c) b (.fpOffset off)) = true := by
  unfold stackArgLoad
  cases c <;> simp only [Reg.homeCls]
  · exact covered_load b n off
  · unfold Cov.Covered; split <;> rfl

/-- No result `mov`s when every result register is a vreg. -/
theorem extraOfT_nil_of_vregs {ctx : Ctx} {results : List Nat} {rss : List (List Reg)}
    (h : ∀ rs ∈ rss, ∀ r ∈ rs, ∃ n c, r = .vreg n c) : extraOfT ctx results rss = [] := by
  unfold extraOfT
  rw [List.filterMap_eq_nil_iff]
  intro ⟨r, rs⟩ hq
  have hv := h rs (List.of_mem_zip hq).2
  simp only
  split
  · rfl
  · rename_i out hne
    obtain ⟨n, c, rfl⟩ := hv out (by simp)
    exact absurd rfl (hne n c)
  · rfl

/-- Every statement's `lower` run emits only covered instructions, and with results returns
them in vregs. -/
def StmtCovT (ctx : Ctx) : Prop :=
  ∀ ii info inst s out s' tr, ctx.insts[ii]? = some info → info.clif = some inst →
    runTerm ctx "lower" [.inst ii] s = .ok (out, s', tr) →
    CovT.CovSince s s' ∧ ∀ rss, out = some (.regsVec rss) → info.results ≠ [] →
      ∀ rs ∈ rss, ∀ r ∈ rs, ∃ n c, r = .vreg n c

/-- Every non-`try_call` terminator of `f`'s run (at its placeholder slot) emits only covered
instructions. -/
def TermCovT (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ B ∈ f.blocks, ∀ ti data targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → B.term.isTry = false →
    termData (abiTerm f B.term) = .ok data →
    termCallF ctx ti data B.term targets s = .ok (out, s', tr) → CovT.CovSince s s'

/-- Every `try_call` terminator of `f`'s run (at its placeholder slot) emits only covered
instructions. -/
def TryCovT (f : Clif.Function) (ctx : Ctx) : Prop :=
  ∀ B ∈ f.blocks, ∀ ti data trs targets s out s' tr, ti < ctx.insts.size →
    ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ → tryCallData f B.term = .ok data →
    tryCallF ctx ti data trs targets s = .ok (out, s', tr) → CovT.CovSince s s'

/-- **Form coverage of the compiled function (typed)**, for input with integer externs whose
VCode is in `prepare`'s domain. Given the ISLE runs' coverage, every instruction of
`prepare (lowerFunction f)` is a control form or `FormOk`. -/
theorem formsCovered_of_runsG {f : Clif.Function} {vc vcp : VCode}
    (hx : f.externs.all (Compile.sigE ·.2.sig) = true) (hpd : Prep.PrepDomain vc)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hrun : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) →
      StmtCovT ctx ∧ TermCovT f ctx ∧ TryCovT f ctx)
    (cx : FnCtx) : FormsCovered cx vcp := by
  obtain ⟨ctx, ranges, st0, bl, hb, hlb, hvb, -, -⟩ := lowerFunction_runT hx hl
  obtain ⟨hS, hT, hY⟩ := hrun ctx ranges st0 hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hlb
  obtain ⟨-, hspec⟩ := lowBlocks_spec hlb
  have hemp := lowBlocks_emptied hlb
  have hstm : ∀ (bi : Nat) (B : Clif.Block) (L : BLow) (j : Nat) (stm : Clif.Stmt) (sl : SLow),
      f.blocks[bi]? = some B → bl[bi]? = some L → B.body[j]? = some stm → L.sl[j]? = some sl →
      (∀ m ∈ sl.st'.emitted.toList, CovT.Covered m = true) ∧ extraOfT ctx stm.results sl.rss = [] := by
    intro bi B L j stm sl hB hL hj hsl
    obtain ⟨-, hc, -, -⟩ := hspec bi B L hB hL
    obtain ⟨info, hi, hic, hres⟩ := hcf.stmt bi B j stm hB hj
    obtain ⟨tr, hrun⟩ := hc j sl hsl
    rw [hstart bi L hL] at hrun
    obtain ⟨⟨ms, hms, hcov⟩, hvr⟩ := hS _ info stm.inst _ _ _ _ hi hic hrun
    refine ⟨?_, ?_⟩
    · rw [hms, hemp L (List.mem_of_getElem? hL) sl (List.mem_of_getElem? hsl)]
      simpa using hcov
    · cases hr : stm.results with
      | nil => simp [extraOfT]
      | cons r rs => exact extraOfT_nil_of_vregs (hvr sl.rss rfl (by rw [hres, hr]; simp))
  have hall := vcBlocksT_all' (fun m => CovT.Covered m = true)
    (fun _ _ hg m h => by rw [coveredT_mapRegs hg]; exact h) (fun _ => rfl)
    (fun n c b off => CovT.covered_of_cov (covered_stackArgLoad n c b off))
    (fun _ => rfl) (f := f) (ctx := ctx) (bl := bl)
    (fun bi B L j stm sl hB hL hj hsl => (hstm bi B L j stm sl hB hL hj hsl).1)
    (fun bi B L j stm sl hB hL hj hsl m hm => by
      rw [(hstm bi B L j stm sl hB hL hj hsl).2] at hm; cases hm)
    (fun bi B L hB hL => by
      obtain ⟨-, -, htst, nl0, nl', hterm⟩ := hspec bi B L hB hL
      obtain ⟨hn, hy⟩ := lowTerm_spec hterm
      have hph := hcf.term bi B hB
      rw [← hstart bi L hL] at hph
      have hti := (Array.getElem?_eq_some_iff.mp hph).1
      have hBm : B ∈ f.blocks := List.mem_of_getElem? hB
      intro m hm
      rcases mem_fixTry hm with hm | ⟨c, ti, rfl⟩
      · cases ht : B.term.isTry with
        | false =>
          obtain ⟨-, hd, out, tr, hc⟩ := hn ht
          obtain ⟨ms, hms, hcov⟩ := hT B hBm _ _ _ _ _ _ _ hti hph ht hd hc
          rw [hms, htst] at hm
          exact hcov m (by simpa using hm)
        | true =>
          obtain ⟨et, het⟩ : ∃ et, IsTryWith B.term et := by
            cases hB' : B.term <;> rw [hB'] at ht <;> simp [Clif.Terminator.isTry] at ht
            · exact ⟨_, .inl ⟨_, _, rfl⟩⟩
            · exact ⟨_, .inr ⟨_, _, rfl⟩⟩
          obtain ⟨T, -, hd, -, -, -, -, out, tr, hc⟩ := hy et het
          obtain ⟨ms, hms, hcov⟩ := hY B hBm _ _ _ _ _ _ _ _ hti hph hd hc
          rw [hms] at hm
          exact hcov m (by simpa using hm)
      · rfl)
  apply formsCovered_of_prepareT hp hpd
  rw [hvb]
  intro vb hvb' i hi
  have := hall vb hvb' i hi
  simpa [CovT.Covered, Bool.or_eq_true, or_assoc] using this

/-- **Form coverage of the compiled function (typed).** Given the ISLE runs' coverage, every
instruction of `prepare (lowerFunction f)` is a control form or `FormOk`. -/
theorem formsCovered_of_runsT {f : Clif.Function} {vc vcp : VCode} (hd : Dominated f)
    (hs : LowerScopeT f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (hrun : ∀ ctx ranges st0, buildCtx f = .ok (ctx, ranges, st0) →
      StmtCovT ctx ∧ TermCovT f ctx ∧ TryCovT f ctx)
    (cx : FnCtx) : FormsCovered cx vcp :=
  formsCovered_of_runsG hs.externsE (Spill.prepDomain_ofT hd hs hl) hl hp hrun cx

/-- **Completeness of `formsCoveredB` on the typed scope**: on input in `Dominated` and
`LowerScopeT` with class-checked float `store`s and `select`s, `prepare (lowerFunction f)` is
covered, for every context. -/
theorem formsCovered_completeT {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) (cx : FnCtx) :
    FormsCovered cx vcp :=
  formsCovered_of_runsT (dominated_of hdom) hs hl hp (fun ctx ranges st0 hb => by
    have hctx : CtxInvT f ctx := ctxInvT_of hs hb
    have hcl : Cov.Clean ctx := clean_of_build hb
    have hfam := CovT.famCover_of hs hdom hst hsel hb
    have hx := externsE_of hs.subsetT
    refine ⟨fun ii info inst s out s' tr hi hc h => ?_, fun B hB ti data targets s out s' tr _ hph _ hd h =>
      CovT.termCall_covT logicImmComplete hctx hcl hfam hph hd
        (CovT.termFam_of hs hdom hb hB (.inl hd)) h,
      fun B hB ti data trs targets s out s' tr _ hph hd h =>
      CovT.tryCall_covT logicImmComplete hctx hcl hfam hph hd
        (CovT.termFam_of hs hdom hb hB (.inr hd)) h⟩
    obtain ⟨h1, h2⟩ := CovT.stmt_covT logicImmComplete hctx hx hcl hfam hi hc h
    refine ⟨h1, fun rss hout hne rs hrs r hr => ?_⟩
    obtain ⟨n, c, hrc, -⟩ := h2 rss hout hne rs hrs r hr
    exact ⟨n, c, hrc⟩) cx

/-- `formsCovered_completeT`, decided: `formsCoveredB` holds of `prepare (lowerFunction f)`. -/
theorem formsCoveredB_completeT {f : Clif.Function} {vc vcp : VCode} (hdom : dominatedB f = true)
    (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true)
    (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) (cx : FnCtx) :
    formsCoveredB cx vcp = true :=
  (formsCoveredB_iff cx vcp).mpr (formsCovered_completeT hdom hs hst hsel hl hp cx)

end Backend.Proof.Driver
