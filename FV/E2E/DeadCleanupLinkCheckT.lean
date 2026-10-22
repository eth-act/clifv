import FV.E2E.DeadCleanupLinkCheck
import FV.E2E.PipelineCheckT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT

/-! # Typed copies of `FV.E2E.DeadCleanupLinkCheck` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupLinkCheck` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefinesT`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

/-- The cleanup checker proves the same linked system contract, with no additional
base-environment, ABI, source or observable-state premise. -/
theorem okBCleanup_soundT {I : LinkInput} (hI : okBCleanup I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (LinkSys.ofInputCleanup I B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup I B F).Img a → F a) :
    (LinkSys.ofInputCleanup I B F).OkT :=
  okRWith_soundT DeadCleanup.prune (.inr rfl) (resultsCleanup_ok I) hI hB hF
end E2E.LinkCheck
