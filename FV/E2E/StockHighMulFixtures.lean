module

public import FV.E2E.StockCmpFixtures

@[expose] public section

namespace E2E.StockHighMulNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false

/-- Signed/unsigned products of original inputs and a large constant, retaining
all earlier source computations in the returned value. -/
def extraBody (config : Configuration) : List Clif.Stmt :=
  let ty := valueType config
  [⟨[4001],.binary .smulhi ty 1 2⟩,
   ⟨[4002],.binary .umulhi ty 1 2⟩,
   ⟨[4003],.binary .smulhi ty 2 304⟩,
   ⟨[4004],.binary .umulhi ty 1 304⟩,
   ⟨[4005],.binary .bxor ty 4001 4002⟩,
   ⟨[4006],.binary .bxor ty 4003 4004⟩,
   ⟨[4007],.binary .bxor ty 4005 4006⟩,
   ⟨[4008],.binary .bxor ty 1196 4007⟩]

def function (config : Configuration) : Clif.Function :=
  let old := StockCmpNIWitness.function config
  {old with name := "stock_highmul_ni",blocks := old.blocks.map fun b =>
    {b with body := b.body ++ extraBody config,term := .ret [4008]}}

def resultValue (config : Configuration) (input : Nat → BitVec (valueType config).width) :
    BitVec (valueType config).width :=
  let constant := BitVec.ofNat (valueType config).width 0x123456789abcdef
  StockCmpNIWitness.resultValue config input ^^^
    ((Clif.Sem.binary .smulhi (input 1) (input 2) ^^^ Clif.Sem.binary .umulhi (input 1) (input 2)) ^^^
      (Clif.Sem.binary .smulhi (input 2) constant ^^^ Clif.Sem.binary .umulhi (input 1) constant))
end E2E.StockHighMulNIWitness
