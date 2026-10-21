import FV.E2E.StockCastFixtures
namespace E2E.StockBitNIWitness
open Backend.Stock.D0
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def extraBody (config : Configuration) : List Clif.Stmt :=
  let ty := valueType config
  let ct := StockShiftNIWitness.countType config
  [⟨[61],.unary .ineg ty 1⟩,⟨[62],.unary .clz ty 1⟩,
   ⟨[63],.unary .ctz ty 2⟩,⟨[64],.unary .bitrev ty 61⟩,
   ⟨[65],.unary .bswap ty 64⟩,⟨[66],.binary .rotl ty 65 2⟩,
   ⟨[67],.binary .rotr ty 66 1⟩,⟨[68],.iconst ct (BitVec.ofNat ct.width 0x105)⟩,
   ⟨[69],.iconst ct (BitVec.ofNat ct.width 0x103)⟩,
   ⟨[70],.binary .rotl ty 67 68⟩,⟨[71],.binary .rotr ty 70 69⟩,
   ⟨[72],.binary .bxor ty 62 63⟩,⟨[73],.binary .bxor ty 71 72⟩,
   ⟨[74],.binary .bxor ty 73 60⟩]

def function (config : Configuration) : Clif.Function :=
  let old := StockCastNIWitness.function config
  {old with name := "stock_bit_ni", blocks := old.blocks.map fun b =>
    {b with body := b.body ++ extraBody config, term := .ret [74]}}

def resultValue (config : Configuration) (input : Nat → BitVec (valueType config).width) :
    BitVec (valueType config).width :=
  let ct := StockShiftNIWitness.countType config
  let swapped := Clif.Sem.unary .bswap (Clif.Sem.unary .bitrev (Clif.Sem.unary .ineg (input 1)))
  let rotated := Clif.Sem.rotr (Clif.Sem.rotl swapped (input 2)) (input 1)
  let immediate := Clif.Sem.rotr (Clif.Sem.rotl rotated (BitVec.ofNat ct.width 0x105))
    (BitVec.ofNat ct.width 0x103)
  (immediate ^^^ (Clif.Sem.unary .clz (input 1) ^^^ Clif.Sem.unary .ctz (input 2))) ^^^
    StockCastNIWitness.resultValue config input

end E2E.StockBitNIWitness
