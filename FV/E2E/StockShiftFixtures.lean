import FV.E2E.StockMulFixtures
namespace E2E.StockShiftNIWitness
open Backend.Stock.D0
set_option autoImplicit false

def countType (config : Configuration) : Clif.Ty :=
  if valueType config == .i64 then .i32 else .i64

/-- Both fused bitfield cases, ordinary register and immediate shifts, shifted
NOT, shared values and omitted work; counts deliberately have the other width. -/
def extraBody (config : Configuration) : List Clif.Stmt :=
  let ty := valueType config
  let ct := countType config
  [⟨[35],.iconst ct (BitVec.ofNat ct.width 0x105)⟩,
   ⟨[36],.iconst ct (BitVec.ofNat ct.width 0x103)⟩,
   ⟨[37],.binary .ishl ty 33 35⟩,⟨[38],.binary .ushr ty 37 36⟩,
   ⟨[39],.iconst ct (BitVec.ofNat ct.width 2)⟩,
   ⟨[40],.iconst ct (BitVec.ofNat ct.width 9)⟩,
   ⟨[41],.binary .ishl ty 33 39⟩,⟨[42],.binary .sshr ty 41 40⟩,
   ⟨[43],.binary .ishl ty 42 2⟩,⟨[44],.binary .ushr ty 43 1⟩,
   ⟨[45],.binary .sshr ty 44 0⟩,⟨[46],.binary .ishl ty 45 39⟩,
   ⟨[47],.unary .bnot ty 46⟩,⟨[48],.binary .bxor ty 47 38⟩,
   ⟨[49],.binary .ishl ty 1 36⟩,⟨[50],.binary .ishl ty 48 35⟩,
   ⟨[51],.binary .bxor ty 50 3⟩,⟨[52],.binary .ushr ty 51 36⟩,
   ⟨[53],.binary .sshr ty 52 40⟩]

def function (config : Configuration) : Clif.Function :=
  let old := StockMulNIWitness.function config
  {old with name := "stock_shift_ni", blocks := old.blocks.map fun b =>
    {b with body := b.body ++ extraBody config, term := .ret [53]}}

def resultValue (config : Configuration) (input : Nat → BitVec (valueType config).width) :
    BitVec (valueType config).width :=
  let width := (valueType config).width
  let unsigned := (StockMulNIWitness.resultValue config input <<< (0x105 % width)) >>> (0x103 % width)
  let signed := (StockMulNIWitness.resultValue config input <<< (2 % width)).sshiftRight (9 % width)
  let lsl := signed <<< (input 2).toNat % width
  let lsr := lsl >>> (input 1).toNat % width
  let asr := lsr.sshiftRight ((input 0).toNat % width)
  let combined := (~~~(asr <<< (2 % width))) ^^^ unsigned
  let immediate := (combined <<< (0x105 % width)) ^^^ input 3
  (immediate >>> (0x103 % width)).sshiftRight (9 % width)
end E2E.StockShiftNIWitness
