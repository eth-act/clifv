import FV.E2E.Statement
import FV.Backend.Proof.PrepareDirect

/-!
# The end-to-end chain without the `prepare` validator

`Compiled` records that `prepCheck` accepted `prepare`'s output. On `PrepDomain` VCode that
premise is a theorem (`Prep.prepCheck_complete`), so `Compiled.of_prepDomain` builds `Compiled`
from the pipeline's results alone: every end-to-end theorem taking `hc : Compiled …`
(`backend_correct_final`, `backend_correct_opt_proven`, `backend_correct_legal`, …) holds with
`Compiled.of_prepDomain …` in place of `hc`, i.e. without the `prepCheck` premise.
`prepDomainB` decides `PrepDomain`.
-/

namespace E2E

open Backend Backend.Proof Backend.Proof.Driver Backend.Proof.Prep

/-- **`prepare` preserves returns and traps** (`PrepareCorrect`) on `PrepDomain` VCode, without
the validator. -/
theorem prepareCorrect_of_domain {sem : Sem} {vc vcp : VCode} (hds : DriverSem sem)
    (h : prepare vc = .ok vcp) (hd : PrepDomain vc) : PrepareCorrect sem vc vcp :=
  fun ρ₀ w₀ => prepare_correct hds h hd ρ₀ w₀

/-- **`Compiled` without the `prepCheck` premise**: the pipeline's results, the lowering
validator, and `PrepDomain` of the lowered VCode. -/
theorem Compiled.of_prepDomain {f : Clif.Function} {k : Nat} {vc vcp : VCode} {rf : RFunc}
    {af : AFunc} {fa : FnAsm} {fb : FnBin} (hl : lowerFunction f = .ok vc)
    (hlo : lowerCheck f vc = true) (hp : Backend.prepare vc = .ok vcp) (hd : PrepDomain vc)
    (hch : checkAlloc vcp rf = .ok ()) (ha : lowerRFunc vcp rf = .ok af)
    (he : emitFunc k af = .ok fa) (hla : fa.layout = .ok fb) : Compiled f k vc vcp rf af fa fb :=
  ⟨hl, hlo, hp, prepCheck_complete hp hd, hch, ha, he, hla⟩

end E2E
