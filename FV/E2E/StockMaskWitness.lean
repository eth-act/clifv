import FV.Backend.Proof.RegallocOperands
import FV.Backend.Proof.SpillLocal
import FV.E2E.StockMaskChecks
import FV.E2E.StockNarrowWitness

namespace E2E.StockMaskNIWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false

/-- Each fixed complete source fixture has the real reusable production
domain, actual raw Stock artifact, preparation, checked allocation, physical
lowering, byte emission and semantic consumer certificate, in both cleanup modes. -/
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
  have fixed := fixed.1.1.1
  change conventions.all _ = true at fixed
  have row := List.all_eq_true.mp fixed config configuration
  have row := List.all_eq_true.mp row (f,ty) member
  simp only [Bool.and_eq_true] at row
  have checked : checks f cleanup = true := by cases cleanup <;> first | exact row.2 | exact row.1.2
  exact StockNarrowNIWitness.compiled_of_checks checked

end E2E.StockMaskNIWitness
