import FV.E2E.StockNotFixtures
namespace E2E.StockMulNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Shared product, both multiply-add mirrors, multiply-subtract and dead
multiply share the complete shipped NOT/constant/logical source body. -/
def extraBody (config : Configuration) : List Clif.Stmt :=
  let ty := valueType config
  [⟨[27],.binary .imul ty 25 2⟩,⟨[28],.binary .iadd ty 27 9⟩,
   ⟨[29],.binary .imul ty 28 1⟩,⟨[30],.binary .iadd ty 8 29⟩,
   ⟨[31],.binary .imul ty 30 2⟩,⟨[32],.binary .isub ty 8 31⟩,
   ⟨[33],.binary .bxor ty 32 27⟩,⟨[34],.binary .imul ty 1 2⟩]

def function (config : Configuration) : Clif.Function :=
  let old := StockNotNIWitness.function config
  {old with name := "stock_mul_ni", blocks := old.blocks.map fun b =>
    {b with body := b.body ++ extraBody config, term := .ret [33]}}

def resultValue (config : Configuration) (input : Nat → BitVec (valueType config).width) :
    BitVec (valueType config).width :=
  let product := StockNotNIWitness.resultValue config input * input 2
  let added := product + BitVec.ofNat (valueType config).width 0x123456789abcdef
  let multiplied := added * input 1
  let addedRight := input 8 + multiplied
  let subtracted := input 8 - addedRight * input 2
  subtracted ^^^ product
end E2E.StockMulNIWitness
