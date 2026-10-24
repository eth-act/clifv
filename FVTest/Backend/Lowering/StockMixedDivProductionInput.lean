import FV.E2E.StockMixedDivFixtures
import FVTest.Backend.Lowering.StockDivProductionInput
import FV.Clif.Print

set_option autoImplicit false
namespace FVTest.StockMixedDivProductionRuntime
open _root_.Backend

def input (config : Stock.D0.Configuration) : String :=
  String.join (E2E.StockDivNIWitness.operations.flatMap fun op =>
    [false,true].map fun safe => (E2E.StockMixedDivNIWitness.function config op safe).print ++ "\n") ++
  FVTest.StockDivProductionRuntime.input config

end FVTest.StockMixedDivProductionRuntime
