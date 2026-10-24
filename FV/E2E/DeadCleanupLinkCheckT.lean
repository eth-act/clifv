import FV.E2E.DeadCleanupLinkCheck
import FV.E2E.PipelineCheckT
import FV.E2E.LinkArmT
import FV.E2E.LinkCheckT
import FV.E2E.LinkCheckFast
import FV.E2E.CalleeWith
import FV.Link.DeadCleanupImage

/-! # Typed copies of `FV.E2E.DeadCleanupLinkCheck` (S11e5 Stage C, slice 8)

The declarations of `FV.E2E.DeadCleanupLinkCheck` that depend on the integer link contract
(`LinkSys.Ok`, `LinkSys.Thm`, `okB`, `ArmRefines`), for the typed contract `LinkSys.OkT`
(suffix `T`; `LinkSys.Ok.*` as `LinkSys.OkT.*`). -/

namespace E2E.LinkCheck
open Backend Backend.Proof Backend.Proof.Driver

def okBCleanupT (I : LinkInput) : Bool := okRWithT DeadCleanup.prune I I.resultsCleanup

/-- **`okBCleanupT` at the size of std**: the same checks with the hash-map context
(`LinkCtx.of`), the program's declared names (`calleeSet`/`calleeWithB`) and the per-function
checks evaluated in parallel tasks (`Link.parMap`); the pipeline runs once. -/
def okBCleanupTFast (I : LinkInput) : Bool :=
  let P := progOf I.resultsCleanup
  let T := tabOf I.resultsCleanup
  let cs := calleeSet P
  let anyInd := P.funcs.any (!indFreeB ·)
  let sy := assocMap I.syms
  (globalChksWith (LinkCtx.of I P T) I P T).all (·.2) &&
    (Link.parMap (fun e => (staticChksWithT DeadCleanup.prune I e.1 e.2 ++
        linkChksWithT (LinkCtx.of I P T) P e.1 e.2 ++
        [("calleeInt", !calleeWithB (fun n => cs.contains n) anyInd (fun n => sy[n]?) e.1 ||
          e.1.sig.returns.all (·.ty.isInt))]).all (·.2)) I.resultsCleanup).all id

theorem okBCleanupTFast_eq (I : LinkInput) : okBCleanupTFast I = okBCleanupT I := by
  simp only [okBCleanupTFast, okBCleanupT, okRWithT, chksWithT, assocMap_fun, globalChksWith_of,
    linkChksWithT_of, calleeIntChk, calleeWithB_eq, Link.parMap_eq, List.all_map,
    Function.comp_def, id]

theorem okBCleanup_globalT {I : LinkInput} (h : okBCleanupT I = true)
    (c : String × Bool) (hc : c ∈ globalChks I (progOf I.resultsCleanup) (tabOf I.resultsCleanup)) :
    c.2 = true := okRWith_globalT DeadCleanup.prune h c hc

theorem okBCleanup_namesT {I : LinkInput} (h : okBCleanupT I = true) :
    ((progOf I.resultsCleanup).funcs.map (·.name)).Nodup := okRWith_namesT DeadCleanup.prune h

theorem factsCleanupT {I : LinkInput} (h : okBCleanupT I = true) {g : Clif.Function}
    (hg : g ∈ (progOf I.resultsCleanup).funcs) :
    FactsWithT DeadCleanup.prune I I.resultsCleanup g (artOf I.resultsCleanup g) :=
  factsRWithT DeadCleanup.prune (resultsCleanup_ok I) h hg

/-- The cleanup checker proves the same linked system contract, with no additional
base-environment, ABI, source or observable-state premise. -/
theorem okBCleanup_soundT {I : LinkInput} (hI : okBCleanupT I = true) {B : BaseEnv}
    {F : BitVec 64 → Prop} (hB : BaseOk (LinkSys.ofInputCleanup I B F))
    (hF : ∀ a, (LinkSys.ofInputCleanup I B F).Img a → F a) :
    (LinkSys.ofInputCleanup I B F).OkT :=
  okRWith_soundT DeadCleanup.prune (.inr rfl) (resultsCleanup_ok I) hI hB hF
end E2E.LinkCheck
