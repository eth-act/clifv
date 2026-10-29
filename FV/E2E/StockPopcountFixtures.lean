module

public import FV.E2E.StockBitFixtures

@[expose] public section

namespace E2E.StockPopcountNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false

def extraBody (config : Configuration) : List Clif.Stmt :=
  let ty := valueType config
  [⟨[75],.unary .popcnt ty 1⟩,⟨[76],.unary .popcnt ty 2⟩,
   ⟨[77],.binary .bxor ty 75 76⟩,⟨[78],.binary .bxor ty 74 77⟩]

def function (config : Configuration) : Clif.Function :=
  let old := StockBitNIWitness.function config
  {old with name := "stock_popcount_ni", blocks := old.blocks.map fun b =>
    {b with body := b.body ++ extraBody config, term := .ret [78]}}

def resultValue (config : Configuration) (input : Nat → BitVec (valueType config).width) :
    BitVec (valueType config).width :=
  StockBitNIWitness.resultValue config input ^^^
    (Clif.Sem.unary .popcnt (input 1) ^^^ Clif.Sem.unary .popcnt (input 2))
end E2E.StockPopcountNIWitness
