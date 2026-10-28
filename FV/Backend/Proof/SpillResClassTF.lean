import FV.Backend.Proof.SpillResClassT
import FV.Backend.Proof.IselCovTFamCoverF

/-!
# `ResClassOk` on the float scope

`resClassOk_of_lowerScopeTF`: `resClassOk_of_lowerScopeT` on the float scope (`LowerScopeTF`)
whose float positions are float-defined (`Compile.floatArgsTyped`): the statements' families
`CovT.famCover_ofF` (the S11f float operations' families 31-35), the `call` results
`CovT.callRes_intF`.
-/

namespace Backend.Proof.Spill

open Backend Backend.Proof Backend.Proof.Driver

/-- **The lowering of a float-scope function returns each statement result in a vreg of its
class.** -/
theorem resClassOk_of_lowerScopeTF {f : Clif.Function} (hdom : dominatedB f = true)
    (hs : LowerScopeTF f) (hfa : Compile.floatArgsTyped f = true)
    (hst : Compile.storeTypedB f = true) (hsel : Compile.selectTypedB f = true) : ResClassOk f := by
  intro ctx ranges st0 bl hb hl bi B L j stm sl hB hL hj hsl k r o c hrk hok
  have hctx : CtxInvT f ctx := ctxInvT_ofF hs hb
  have hcf := ctxFacts_of hb
  obtain ⟨-, hstart⟩ := lowBlocks_start hl
  obtain ⟨-, hc, -, -⟩ := (lowBlocks_spec hl).2 bi B L hB hL
  obtain ⟨info, hi, hic, hres⟩ := hcf.stmt bi B j stm hB hj
  obtain ⟨tr, hrun⟩ := hc j sl hsl
  rw [hstart bi L hL] at hrun
  have hr : r ∈ info.results := by rw [hres]; exact List.mem_of_getElem? hrk
  have hne : info.results ≠ [] := List.ne_nil_of_mem hr
  have hfam := CovT.famCover_ofF hs hfa hdom hst hsel hb
  obtain ⟨n, c', hn, hcase⟩ := (CovT.stmt_covT Cov.logicImmComplete hctx hs.externsE
    (Cov.clean_of_build hb) hfam hi hic hrun).2 sl.rss rfl hne [.vreg o c]
    (List.mem_of_getElem? hok) (.vreg o c) (List.mem_singleton_self _)
  cases hn
  rcases hcase with ⟨hcall, rfl⟩ | hall
  · exact CovT.callRes_intF hs hdom hb hi hic hcall r hr
  · exact hall r hr

end Backend.Proof.Spill
