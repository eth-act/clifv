import FV.Backend.Proof.StockMemorySretCopyCheck
import FV.Backend.Proof.StockMemorySretCopyDomain
import FV.Backend.Proof.StockMemorySretCopyBodyWitness

namespace Backend.Stock.MemorySretCopy.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory
open Backend.Stock.Memory.StoreRoots.ComputedFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private def observed : Bool :=
  sourceOk function && (Stock.lower function).toOption.any
    (fun result => MemoryStoreCfg.effectsOnly result.code)

private theorem observed_true : observed = true := by native_decide

/-- The original captured sret source passes admission without a signature rewrite. -/
theorem captured_sret_sourceOk_witness : sourceOk function = true :=
  (Bool.and_eq_true_iff.mp observed_true).1

/-- The unchanged captured function has a checked Stock artifact and complete ABI-aware correctness. -/
theorem captured_sret_check_witness : ∃ result,
    Stock.lower function = .ok result ∧ check function result.code = true ∧
      SretCopy.CfgClass function ∧ DomainABI function := by
  have h := observed_true
  unfold observed at h
  obtain ⟨source,effects⟩ := Bool.and_eq_true_iff.mp h
  cases run : Stock.lower function with
  | error message => simp only [run,Except.toOption,Option.any_none] at effects; cases effects
  | ok result =>
    simp only [run,Except.toOption,Option.any_some] at effects
    have family := sourceOk_sound source
    refine ⟨result,rfl,?_,family,family.domainABI⟩
    simp only [check,source,run,decide_true,Bool.true_and,effects]

end Backend.Stock.MemorySretCopy.Fixture
