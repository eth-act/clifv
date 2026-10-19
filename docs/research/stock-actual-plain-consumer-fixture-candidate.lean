import StockActualModesProbe
import Crates.StockD0MixedPlain

/-! Fixed generated-program witness using the new actual-callback entrypoints.
The existing generated fixture's finite native checks are reused; this does not
replace universal configuration/name/oracle witnesses. -/
namespace FVTest.StockActualPlainConsumer
open E2E E2E.LinkCheck E2E.BinCheck Backend

-- witness: native_decide (through the fixed generated fixture)
theorem actual_results (I : LinkInput) :
    I.resultsWithLowering Stock.D0.defaultLower id = I.results := by
  rfl

-- witness: native_decide
theorem actual_checks :
    okRWith id Crates.StockD0MixedPlain.input
      (Crates.StockD0MixedPlain.input.resultsWithLowering Stock.D0.defaultLower id) = true := by
  rw [actual_results]
  exact Crates.StockD0MixedPlain.okB_input

-- witness: native_decide
theorem actual_stock_correct :
    CrateStmtWithCompilerModes Crates.StockD0MixedPlain.input Stock.D0.defaultLower id "stock_identity" :=
  crate_correct_withCompilerModes _ _ _ (Or.inl rfl) actual_checks _

-- witness: native_decide
theorem actual_legacy_caller_correct :
    CrateStmtWithCompilerModes Crates.StockD0MixedPlain.input Stock.D0.defaultLower id "legacy_caller" :=
  crate_correct_withCompilerModes _ _ _ (Or.inl rfl) actual_checks _

-- witness: native_decide
theorem actual_binary (file : ByteArray) (h : Elf.Agrees file Crates.StockD0MixedPlain.exAll) :
    BinOkWithResults Crates.StockD0MixedPlain.input
      (Crates.StockD0MixedPlain.input.resultsWithLowering Stock.D0.defaultLower id)
      Crates.StockD0MixedPlain.dataObjs file := by
  rw [actual_results]
  exact (Crates.StockD0MixedPlain.bin_ok file h).toWithResults

#print axioms actual_results
#print axioms actual_checks
#print axioms actual_stock_correct
#print axioms actual_legacy_caller_correct
#print axioms actual_binary
end FVTest.StockActualPlainConsumer
