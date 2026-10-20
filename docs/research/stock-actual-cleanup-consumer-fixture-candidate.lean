import StockActualModesProbe
import Crates.StockD0MixedCleanup
import FV.E2E.DeadCleanupBinCheck

/-! Fixed generated-program witness using the new actual-callback entrypoints.
The existing generated fixture's finite native checks are reused; this does not
replace universal configuration/name/oracle witnesses. -/
namespace FVTest.StockActualCleanupConsumer
open E2E E2E.LinkCheck E2E.BinCheck Backend

-- witness: native_decide (through the fixed generated fixture)
theorem actual_results (I : LinkInput) :
    I.resultsWithLowering Stock.D0.defaultLower Backend.DeadCleanup.prune = I.resultsCleanup := by
  rfl

-- witness: native_decide
theorem actual_checks :
    okRWith Backend.DeadCleanup.prune Crates.StockD0MixedCleanup.input
      (Crates.StockD0MixedCleanup.input.resultsWithLowering Stock.D0.defaultLower Backend.DeadCleanup.prune) = true := by
  rw [actual_results]
  exact Crates.StockD0MixedCleanup.okB_input

-- witness: native_decide
theorem actual_stock_correct :
    CrateStmtWithCompilerModes Crates.StockD0MixedCleanup.input Stock.D0.defaultLower Backend.DeadCleanup.prune "stock_identity" :=
  crate_correct_withCompilerModes _ _ _ (Or.inr rfl) actual_checks _

-- witness: native_decide
theorem actual_legacy_caller_correct :
    CrateStmtWithCompilerModes Crates.StockD0MixedCleanup.input Stock.D0.defaultLower Backend.DeadCleanup.prune "legacy_caller" :=
  crate_correct_withCompilerModes _ _ _ (Or.inr rfl) actual_checks _

-- witness: native_decide
theorem actual_binary (file : ByteArray) (h : Elf.Agrees file Crates.StockD0MixedCleanup.exAll) :
    BinOkWithResults Crates.StockD0MixedCleanup.input
      (Crates.StockD0MixedCleanup.input.resultsWithLowering Stock.D0.defaultLower Backend.DeadCleanup.prune)
      Crates.StockD0MixedCleanup.dataObjs file := by
  rw [actual_results]
  have old := Crates.StockD0MixedCleanup.bin_ok file h
  exact ⟨old.static, old.code, old.data, old.syms⟩

#print axioms actual_results
#print axioms actual_checks
#print axioms actual_stock_correct
#print axioms actual_legacy_caller_correct
#print axioms actual_binary
end FVTest.StockActualCleanupConsumer
