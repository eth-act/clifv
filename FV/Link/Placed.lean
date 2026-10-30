import FV.Link.Image
import FV.E2E.DeadCleanupLinkCheck

/-! # The Lean compiler's layout, computed by the driver (L1g, #228)

The totality theorems are stated for the Lean compiler's layout: `LinkSpec.placed`
(`FV/Link/ExeInput.lean`) and `DeadCleanup.placed` (`FV/Link/ExeInputCleanup.lean`), the spec with
the names of its CLIF functions and the sizes of their compiled code. `lake exe lean-link` compiles
`placedPar` of the bundle's spec: the same layout with the functions compiled in parallel tasks
(`placedPar_eq`, `FV/Link/PlacedEq.lean`), so the spec it compiles is the theorems' by construction
and no size is read from outside. Kept free of proofs so that `lean-link` runs it.
-/

namespace Link

open E2E.LinkCheck

/-- `LinkSpec.placed` with the functions compiled in parallel tasks (`LinkSpec.placedPar_eq`). -/
def LinkSpec.placedPar (S : LinkSpec) : LinkSpec :=
  { S with names := S.funcs.map (·.func.name),
           sizes := parMap (fun fi => (getOk (pipeT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size)
             S.funcs }

/-- `DeadCleanup.placed` with the functions compiled in parallel tasks
(`DeadCleanup.placedPar_eq`). -/
def DeadCleanup.placedPar (S : LinkSpec) : LinkSpec :=
  { S with names := S.funcs.map (·.func.name),
           sizes := parMap
             (fun fi => (getOk (pipeCleanupT fi.func fi.k 0 (raJ fi.ra fi.j))).fb.words.size) S.funcs }

end Link
