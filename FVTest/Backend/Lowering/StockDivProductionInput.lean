import FVTest.Backend.Lowering.StockScalarTestSupport
import FV.Backend.Lowering.StockPrologue
import FV.Backend.Lowering.StockScalarAdd
import FV.E2E.StockLogicalFixtures
import FV.E2E.StockScalarFixtures
import FV.E2E.StockHighMulFixtures
import FV.E2E.StockDivFixtures
import FV.Clif.Print

set_option autoImplicit false
namespace FVTest.StockDivProductionRuntime
open _root_.Backend

def input (config : Stock.D0.Configuration) : String :=
  String.join (E2E.StockDivNIWitness.operations.map fun op =>
    (E2E.StockDivNIWitness.function config op).print ++ "\n") ++
  (E2E.StockHighMulNIWitness.function config).print ++ "\n" ++
  ({E2E.StockCmpNIWitness.function config with name := "retained_cmp"}).print ++ "\n" ++
  ({E2E.StockMinMaxNIWitness.function config with name := "retained_minmax"}).print ++ "\n" ++
  ({E2E.StockPopcountNIWitness.function config with name := "retained_popcount"}).print ++ "\n" ++
  ({E2E.StockBitNIWitness.function config with name := "retained_bit"}).print ++ "\n" ++
  ({E2E.StockCastNIWitness.function config with name := "retained_cast"}).print ++ "\n" ++
  ({E2E.StockShiftNIWitness.function config with name := "retained_shift"}).print ++ "\n" ++
  ({E2E.StockMulNIWitness.function config with name := "retained_mul"}).print ++ "\n" ++
  ({E2E.StockNotNIWitness.function config with name := "retained_not"}).print ++ "\n" ++
  ({E2E.StockScalarNIWitness.function config with name := "retained_constant"}).print ++ "\n" ++
  ({E2E.StockLogicalNIWitness.function config with name := "retained_logical"}).print ++ "\n" ++
  ({E2E.StockMixedNIWitness.function config with name := "retained_mixed"}).print ++ "\n" ++
  ({E2E.StockArithmeticNIWitness.function config with name := "retained_arithmetic"}).print ++ "\n" ++
  (Stock.ScalarAdd.source "retained_scalar" config []).print ++ "\n" ++
  (Stock.Prologue.source "retained_prologue" .systemVI64 []).print ++ "\n" ++
  (Stock.D0.source "retained_d0" .fastI32 []).print ++ "\n" ++
  FVTest.StockScalarFixture.legacySource "retained_legacy"

end FVTest.StockDivProductionRuntime
