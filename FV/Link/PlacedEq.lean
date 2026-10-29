module

public import FV.Link.Placed
public import FV.Link.ExeInput
public import FV.Link.ExeInputCleanup

@[expose] public section

/-! # The driver's layout is the theorems' (L1g, #228)

`lean-link` compiles `placedPar S` (`FV/Link/Placed.lean`): it is `S.placed` (`placedPar_eq`),
the layout `Link.compileExe_total_reach` and `Link.compileExe_correct*` are about, and a fixpoint
of `placed` (`placed_placedPar`: the hypothesis `S.placed = S` of `placed_of_compileExe` holds by
construction). The same for the shipped compiler (`DeadCleanup.placed`).
-/

namespace Link

open E2E.LinkCheck

theorem LinkSpec.placedPar_eq (S : LinkSpec) : S.placedPar = S.placed := by
  simp only [LinkSpec.placedPar, LinkSpec.placed, LinkSpec.withSizes, LinkSpec.sizesOf, parMap_eq]

theorem DeadCleanup.placedPar_eq (S : LinkSpec) : DeadCleanup.placedPar S = DeadCleanup.placed S := by
  simp only [DeadCleanup.placedPar, DeadCleanup.placed, LinkSpec.withSizes, DeadCleanup.sizesOf,
    parMap_eq]

/-- **The driver's spec is a fixpoint of the layout**: compiling `placedPar S` is compiling with
the Lean compiler's layout of itself. -/
theorem LinkSpec.placed_placedPar (S : LinkSpec) : S.placedPar.placed = S.placedPar := by
  simp only [LinkSpec.placedPar_eq, LinkSpec.placed, LinkSpec.withSizes, LinkSpec.sizesOf]

theorem DeadCleanup.placed_placedPar (S : LinkSpec) :
    DeadCleanup.placed (DeadCleanup.placedPar S) = DeadCleanup.placedPar S := by
  simp only [DeadCleanup.placedPar_eq, DeadCleanup.placed, LinkSpec.withSizes, DeadCleanup.sizesOf]

end Link
