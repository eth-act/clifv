import FV.Backend.Proof.RelocProvTab
import FV.Backend.Proof.IselFlowRootF

/-!
# The root rules of `lower` and `lower_branch` against the name-provenance table (#216)

The closure's root rules of `lower` (`data_program.r686`, in the chunks `Flow.flowRules0`… of
`IselFlowRootF`, to bound the kernel's memory) check strictly against `provTab` with a
name-free root instruction (`NA.c0`); so do all rules of `lower_branch` (`data_program.r687`),
with a name-free instruction and block list. The result is unconstrained (`NA.top`): what the
provenance proof needs is the strict `emit` precondition along the way.
-/

namespace Backend.Proof.RelocProv

open Isle Isle.Aarch64 Backend.Proof

/-- The check of one root rule of `lower`: rules outside the closure are not checked. -/
def provRootOk (r : Rule) : Bool :=
  !closureRootIds.contains r.id || aRule program provTab true [NA.c0] NA.top r

set_option maxRecDepth 100000 in
theorem provRules0_ok : Flow.flowRules0.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules1_ok : Flow.flowRules1.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules2_ok : Flow.flowRules2.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules3_ok : Flow.flowRules3.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules4_ok : Flow.flowRules4.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules5_ok : Flow.flowRules5.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules6_ok : Flow.flowRules6.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules7_ok : Flow.flowRules7.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules8_ok : Flow.flowRules8.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules9_ok : Flow.flowRules9.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules10_ok : Flow.flowRules10.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules11_ok : Flow.flowRules11.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules12_ok : Flow.flowRules12.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules13_ok : Flow.flowRules13.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules14_ok : Flow.flowRules14.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules15_ok : Flow.flowRules15.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules16_ok : Flow.flowRules16.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules17_ok : Flow.flowRules17.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules18_ok : Flow.flowRules18.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules19_ok : Flow.flowRules19.all provRootOk = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem provRules20_ok : Flow.flowRules20.all provRootOk = true := by
  decide +kernel

/-- Every closure root rule of `lower` checks strictly. -/
theorem provRoot_ok : (program.rulesOf TId.lower).all provRootOk = true := by
  rw [Flow.flowRules_eq]
  simp only [List.all_append, provRules0_ok, provRules1_ok, provRules2_ok, provRules3_ok, provRules4_ok, provRules5_ok, provRules6_ok, provRules7_ok, provRules8_ok, provRules9_ok, provRules10_ok, provRules11_ok, provRules12_ok, provRules13_ok, provRules14_ok, provRules15_ok, provRules16_ok, provRules17_ok, provRules18_ok, provRules19_ok, provRules20_ok, Bool.and_self]

set_option maxRecDepth 100000 in
/-- Every rule of `lower_branch` checks strictly. -/
theorem provRootBranch_ok : (program.rulesOf TId.lower_branch).all
    (aRule program provTab true [NA.c0, NA.c0] NA.top) = true := by
  rw [show TId.lower_branch = 687 from rfl, data_program.r687]
  decide +kernel

end Backend.Proof.RelocProv
