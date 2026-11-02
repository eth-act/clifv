import FV.Backend.Proof.IselCovTDriver
import FV.Backend.Proof.IselCovTFamCover
import FV.Backend.Proof.SpillClassesT

/-!
# `ResClassOk` on the typed scope

`resClassOk_of_lowerScopeT`: on input in `dominatedB` and the typed scope `LowerScopeT` with
class-checked float `store`s and `select`s, a statement's `lower` returns each result in a vreg
of the result's class (`ResClassOk`), so `resClassOkB` holds (`resClassOkB_of_lowerScopeT`).
The typed coverage analysis gives the result registers (`CovT.stmt_covT`: the family's one
result class, `famOut`), the `call` rules' int vregs are int-class results
(`CovT.callRes_int`). `resClassOk_of_lowerScope` (subset E) is unchanged.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-- **The typed lowering returns each statement result in a vreg of its class.** -/
theorem resClassOk_of_lowerScopeT {f : Clif.Function} (hdom : dominatedB f = true)
    (hs : LowerScopeT f) (hst : Compile.storeTypedB f = true)
    (hsel : Compile.selectTypedB f = true) : ResClassOk f := by
  intro ctx ranges st0 bl hb hl bi B L j stm sl hB hL hj hsl k r o c hrk hok
  have hctx : CtxInvT f ctx := ctxInvT_of hs hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hl
  obtain ⟨-, hc, -, -⟩ := (lowBlocks_spec hl).2 bi B L hB hL
  obtain ⟨info, hi, hic, hres⟩ := hcf.stmt bi B j stm hB hj
  obtain ⟨tr, hrun⟩ := hc j sl hsl
  rw [hstart bi L hL] at hrun
  have hr : r ∈ info.results := by rw [hres]; exact List.mem_of_getElem? hrk
  have hne : info.results ≠ [] := List.ne_nil_of_mem hr
  have hfam := CovT.famCover_of hs hdom hst hsel hb
  obtain ⟨n, c', hn, hcase⟩ := (CovT.stmt_covT Cov.logicImmComplete hctx (externsE_of hs.subsetT)
    (Cov.clean_of_build hb) hfam hi hic hrun).2 sl.rss rfl hne [.vreg o c]
    (List.mem_of_getElem? hok) (.vreg o c) (List.mem_singleton_self _)
  cases hn
  rcases hcase with ⟨hcall, rfl⟩ | hall
  · exact CovT.callRes_int hs hdom hb hi hic hcall r hr
  · exact hall r hr

end Backend.Proof.Spill
