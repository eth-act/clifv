import FV.Backend.Lowering.StockD0

namespace E2E.StockLogicalNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- All three logical operators, selection/subtraction, an actual stack argument,
unused parameters, an explicit slot and an omitted dead operation. -/
def function (config : Configuration) : Clif.Function :=
  let ty := valueType config
  {source "stock_logical_ni" config [] with
    sig := {
      params := List.replicate 9 ⟨ty,.none,.normal⟩
      returns := [⟨ty,.none,.normal⟩]
      callConv := convention config}
    slots := [(7,⟨8,some 8⟩)]
    blocks := [{
      id := 0
      params := (List.range 9).map (fun i => (i,ty))
      body := [⟨[9],.binary .band ty 1 8⟩,⟨[10],.binary .bxor ty 9 2⟩,
        ⟨[11],.binary .bor ty 10 1⟩,⟨[12],.select ty 0 11 9⟩,
        ⟨[13],.binary .isub ty 12 2⟩,⟨[14],.binary .band ty 1 8⟩]
      term := .ret [13]}]}


end E2E.StockLogicalNIWitness
