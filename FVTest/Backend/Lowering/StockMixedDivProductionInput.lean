module

public import FV.E2E.StockMixedDivFixtures
public import FVTest.Backend.Lowering.StockDivProductionInput
public import FV.Clif.Print

@[expose] public section

set_option autoImplicit false
namespace FVTest.StockMixedDivProductionRuntime
open _root_.Backend

def input (config : Stock.D0.Configuration) : String :=
  String.join (E2E.StockDivNIWitness.operations.flatMap fun op =>
    [false,true].map fun safe => (E2E.StockMixedDivNIWitness.function config op safe).print ++ "\n") ++
  FVTest.StockDivProductionRuntime.input config

end FVTest.StockMixedDivProductionRuntime
