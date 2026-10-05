import FV.Backend.Proof.IselCovDriver
import FV.Backend.Proof.LowerCover
import FV.Backend.Proof.LogicImmComplete

/-!
# Form coverage without `formsCoveredB` (V3)

`formsCovered_complete`: on input in `LowerScope`, every instruction of `prepare`'s output of
`lowerFunction`'s VCode is a control form or a covered straight-line form (`FormsCovered`), so
the end-to-end theorems' `hcov` premise is a theorem (`E2E.backend_correct_final_of_lower`).
The driver's ISLE runs are covered (`stmt_cov`, `termCall_cov`, `tryCall_cov`: the abstract
interpretation of `IselCov*`, decided once over the exported rule data), the driver's own
instructions and its renaming keep coverage, and so does `prepare` (`formsCovered_of_runs`).
The ISLE-level lemmas take `hLI : LogicImmComplete` (the emitter encodes every logical
immediate `ImmLogic.ofNat?` accepts); it is discharged here by `logicImmComplete`.
-/

namespace Backend.Proof.Driver

open Backend Backend.Proof Backend.Proof.Cov

/-- **Completeness of `formsCoveredB`**: on `LowerScope` input, `prepare (lowerFunction f)` is
covered, for every context. -/
theorem formsCovered_complete {f : Clif.Function} {vc vcp : VCode}
    (hs : LowerScope f) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp) (cx : FnCtx) :
    FormsCovered cx vcp :=
  formsCovered_of_runs hs hl hp (fun ctx _ _ hb => by
    have hctx : CtxInv f ctx := ctxOk_sound (ctxOk_complete hs hb)
    have hcl : Cov.Clean ctx := clean_of_build hb
    exact ⟨fun _ _ _ _ _ _ _ hi hc h => stmt_cov logicImmComplete hctx hcl hi hc h,
      fun _ _ _ _ _ _ _ _ _ hph _ hd h => termCall_cov logicImmComplete hctx hcl hph hd h,
      fun _ _ _ _ _ _ _ _ _ _ hph hd h => tryCall_cov logicImmComplete hctx hcl hph hd h⟩) cx

/-- `formsCovered_complete` with the input condition decided. -/
theorem formsCovered_completeB {f : Clif.Function} {vc vcp : VCode}
    (hs : lowerScopeB f = true) (hl : lowerFunction f = .ok vc) (hp : prepare vc = .ok vcp)
    (cx : FnCtx) : FormsCovered cx vcp :=
  formsCovered_complete (lowerScope_of hs) hl hp cx

end Backend.Proof.Driver
