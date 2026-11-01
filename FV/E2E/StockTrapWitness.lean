import FV.E2E.StockMaskFixtures
import FV.E2E.StockNarrowWitness

/-! Production witness of the scalar route on functions that end in `trap`: fixed mask-family
bodies (with divisions that can trap first) and a bare terminator, in every calling convention
and both cleanup modes. The fixed checks run the actual classifier, Stock lowering, paired
checks, preparation, allocation, physical lowering and emission. -/

namespace E2E.StockTrapNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

abbrev conventions := StockNarrowNIWitness.conventions
abbrev widths := StockMaskNIWitness.widths

/-- The mixed mask body (divisions, bmask, nop) ending in `trap`: sample 0 traps in a division,
sample 1 runs the whole body and traps at the terminator. -/
def mixedFunction (config : Configuration) (ty : Clif.Ty) : Clif.Function :=
  let f := StockMaskNIWitness.mixedFunction config ty ty
  {f with name := f.name ++ "_trap",blocks := [{f.blocks[0]! with term := .trap (.user 9)}]}

/-- Only the terminator: the Stock code is the entry prelude and `udf`. -/
def bareFunction (config : Configuration) (ty : Clif.Ty) : Clif.Function :=
  let f := StockMaskNIWitness.function config ty ty
  {f with name := f.name ++ "_bare_trap",blocks := [{f.blocks[0]! with body := [],term := .trap (.user 9)}]}

def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  let all := widths.flatMap fun ty => [(mixedFunction config ty,ty),(bareFunction config ty,ty)]
  all.zipIdx.map fun ((f,ty),i) => ({f with name := s!"stock_trap_{i}"},ty)

abbrev checks := StockNarrowNIWitness.checks

def grid : Bool := conventions.all fun config =>
  (functions config).all fun (f,_) => checks f false && checks f true

/-- The source traps in the body or at the terminator, with the original codes. -/
def sourceTraps : Bool := conventions.all fun config => widths.all fun ty =>
  StockNarrowNIWitness.trapped .intDivz (StockNarrowNIWitness.sourceRun (mixedFunction config ty) ty 0) &&
  StockNarrowNIWitness.trapped (.user 9) (StockNarrowNIWitness.sourceRun (mixedFunction config ty) ty 1) &&
  StockNarrowNIWitness.trapped (.user 9) (StockNarrowNIWitness.sourceRun (bareFunction config ty) ty 1)

-- witness: native_decide (fixed actual pipelines and source runs only)
theorem checks_true : (grid && sourceTraps) = true := by native_decide

/-- Each fixed function that ends in `trap` has the scalar production domain, the actual raw
Stock artifact, preparation, checked allocation, physical lowering, byte emission and semantic
consumer certificate, in both cleanup modes. -/
theorem compiled_cases {config : Configuration} (configuration : config ∈ conventions)
    {f : Clif.Function} {ty : Clif.Ty} (member : (f,ty) ∈ functions config) (cleanup : Bool) :
    Stock.Scalar.Domain f ∧
    ∃ result vcp rf af fa fb,
      CompiledStockArithmeticStage f cleanup 0 result vcp rf af fa fb ∧
      CompiledSemanticNI f 0 result.code vcp rf af fa fb ∧
      Stock.Scalar.lowerValidated f = .ok result.code ∧
      DivBoundary.check f.sig result.code = true ∧
      leanAlloc vcp = .ok rf ∧ FormsCovered ⟨fa.k,af.slotBase⟩ vcp := by
  have fixed := checks_true
  simp only [Bool.and_eq_true] at fixed
  have row := List.all_eq_true.mp fixed.1 config configuration
  have row := List.all_eq_true.mp row (f,ty) member
  simp only [Bool.and_eq_true] at row
  have checked : checks f cleanup = true := by cases cleanup <;> first | exact row.2 | exact row.1
  exact StockNarrowNIWitness.compiled_of_checks checked

end E2E.StockTrapNIWitness
