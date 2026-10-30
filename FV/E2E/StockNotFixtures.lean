import FV.Backend.Lowering.StockD0

namespace E2E.StockNotNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Plain NOT, NOT-of-XOR and NOT/logical look-through share a complete
constant/mixed source body, with dead producers, nine parameters,
an actual stack argument, and an explicit slot. -/
def function (config : Configuration) : Clif.Function :=
  let ty := valueType config
  {source "stock_not_ni" config [] with
    sig := {
      params := List.replicate 9 ⟨ty,.none,.normal⟩
      returns := [⟨ty,.none,.normal⟩]
      callConv := convention config}
    slots := [(7,⟨8,some 8⟩)]
    blocks := [{
      id := 0
      params := (List.range 9).map (fun i => (i,ty))
      body := [⟨[9],.iconst ty (BitVec.ofNat ty.width 0x123456789abcdef)⟩,
        ⟨[10],.iconst ty (BitVec.ofNat ty.width 4097)⟩,
        ⟨[11],.binary .iadd ty 1 9⟩,⟨[12],.binary .band ty 11 8⟩,
        ⟨[13],.binary .bxor ty 12 2⟩,⟨[14],.binary .bor ty 13 9⟩,
        ⟨[15],.select ty 0 14 12⟩,⟨[16],.binary .isub ty 15 2⟩,
        ⟨[17],.binary .iadd ty 16 10⟩,
        ⟨[18],.iconst ty (BitVec.ofNat ty.width 42)⟩,
        ⟨[19],.binary .band ty 1 8⟩,
        ⟨[20],.unary .bnot ty 17⟩,⟨[21],.binary .bxor ty 20 2⟩,
        ⟨[22],.unary .bnot ty 21⟩,⟨[23],.binary .iadd ty 22 10⟩,
        ⟨[24],.binary .band ty 23 8⟩,⟨[25],.unary .bnot ty 24⟩,
        ⟨[26],.unary .bnot ty 1⟩]
      term := .ret [25]}]}

/-- Independent reference expression over arbitrary original inputs. -/
def resultValue (config : Configuration) (input : Nat → BitVec (valueType config).width) :
    BitVec (valueType config).width :=
  let constant := BitVec.ofNat (valueType config).width 0x123456789abcdef
  let band := (input 1 + constant) &&& input 8
  let selected := Clif.Sem.select (input 0) ((band ^^^ input 2) ||| constant) band
  let previous := selected - input 2 + BitVec.ofNat (valueType config).width 4097
  let inverted := Clif.Sem.unary .bnot previous
  let xor := inverted ^^^ input 2
  let complemented := Clif.Sem.unary .bnot xor
  Clif.Sem.unary .bnot ((complemented + BitVec.ofNat (valueType config).width 4097) &&& input 8)
end E2E.StockNotNIWitness
