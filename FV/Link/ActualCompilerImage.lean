import FV.Link.ActualImage
import FV.E2E.ActualCompilerModes

/-! Feed the actual lowering callback's results into the existing checked byte
writer, retaining function/oracle indices, allocation mode and source names.
The old linker instances remain available with exact compatibility. -/
set_option autoImplicit false
namespace Link
open E2E E2E.LinkCheck Backend

/-- The compiler's actual result table, evaluated once in parallel. -/
def parResultsWithLowering (I : LinkInput)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode) : Res :=
  parMap (fun fi => (fi.func, I.pipeOfWithLowering lower stage fi)) I.funcs

theorem parResultsWithLowering_eq (I : LinkInput)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode) :
    parResultsWithLowering I lower stage = I.resultsWithLowering lower stage := by
  simp only [parResultsWithLowering, parMap_eq, LinkInput.resultsWithLowering]

/-- Placement and stack depth are computed from this same actual result table. -/
def LinkSpec.inputWithLowering (S : LinkSpec)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode) : LinkInput :=
  S.input0.withDepth (S.input0.resultsWithLowering lower stage)

theorem LinkSpec.inputWithLowering_results (S : LinkSpec)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode) :
    (S.inputWithLowering lower stage).resultsWithLowering lower stage =
      S.input0.resultsWithLowering lower stage := by
  rfl

/-- Compile through the callback and write exactly its table, retaining every
existing placement, relocation, code-map, ELF and outside-image check. -/
def leanLinkWithLowering (S : LinkSpec) (file0 : ByteArray)
    (lower : Clif.Function → Except String VCode) (stage : Clif.Function → VCode → VCode) :
    Except String ByteArray :=
  leanLinkWithResults S file0 (fun I => parResultsWithLowering I lower stage)

/-- Exact legacy-instance results and errors, for arbitrary source and ELF input. -/
theorem leanLinkWithLowering_plain (S : LinkSpec) (file0 : ByteArray) :
    leanLinkWithLowering S file0 Stock.D0.defaultLower (fun _ => id) = leanLink S file0 := by
  rfl

/-- Exact cleanup-instance results and errors, for arbitrary source and ELF input. (The stage is
the production cleanup stage `cleanupStage`, formerly `fun _ => DeadCleanup.prune`: the
compiler now runs Cranelift's skip of unused instructions.) -/
theorem leanLinkWithLowering_cleanup (S : LinkSpec) (file0 : ByteArray) :
    leanLinkWithLowering S file0 Stock.D0.defaultLower cleanupStage =
      DeadCleanup.leanLink S file0 := by
  rfl
end Link
