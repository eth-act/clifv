import FV.Backend.Lowering.StockD0

namespace E2E.StockScalarNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Two live constants, including multi-word materialization and a shared
logical operand; both dead constants and prior pure families, nine parameters,
an actual stack argument, and an explicit slot. -/
def function (config : Configuration) : Clif.Function :=
  let ty := valueType config
  {source "stock_scalar_ni" config [] with
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
        ⟨[19],.binary .band ty 1 8⟩]
      term := .ret [17]}]}

end E2E.StockScalarNIWitness
