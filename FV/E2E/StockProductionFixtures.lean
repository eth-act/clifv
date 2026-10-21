import FV.Backend.Lowering.StockD0

/-! Shared source fixtures for runtime tests and proof witnesses. -/
open Backend.Stock.D0
set_option autoImplicit false

namespace E2E.StockArithmeticNIWitness

/-- Two arithmetic operations, an actually read ninth stack parameter, six
unused parameters and an explicit source slot, across all six shipped ABIs. -/
def function (config : Configuration) : Clif.Function :=
  let ty := valueType config
  {source "stock_arithmetic_ni" config [] with
    sig := {
      params := List.replicate 9 ⟨ty,.none,.normal⟩
      returns := [⟨ty,.none,.normal⟩]
      callConv := convention config}
    slots := [(7,⟨8,some 8⟩)]
    blocks := [{
      id := 0
      params := (List.range 9).map (fun i => (i,ty))
      body := [⟨[9],.binary .iadd ty 0 8⟩,⟨[10],.binary .isub ty 9 1⟩]
      term := .ret [10]}]}

end E2E.StockArithmeticNIWitness

namespace E2E.StockMixedNIWitness

/-- Dependent add/select/sub, a consumed ninth stack argument, five unused
parameters, an explicit source slot and an omitted dead operation. -/
def function (config : Configuration) : Clif.Function :=
  let ty := valueType config
  {source "stock_mixed_ni" config [] with
    sig := {
      params := List.replicate 9 ⟨ty,.none,.normal⟩
      returns := [⟨ty,.none,.normal⟩]
      callConv := convention config}
    slots := [(7,⟨8,some 8⟩)]
    blocks := [{
      id := 0
      params := (List.range 9).map (fun i => (i,ty))
      body := [⟨[9],.binary .iadd ty 1 8⟩,⟨[10],.select ty 0 9 1⟩,
        ⟨[11],.binary .isub ty 10 2⟩,⟨[12],.binary .iadd ty 1 8⟩]
      term := .ret [11]}]}

end E2E.StockMixedNIWitness
