module

public import FV.Backend.Lowering.StockD0

public section

/-! Input-only shape for the next complete function class. Production selection
is added only after the universal proofs and consumers are connected. -/
set_option autoImplicit false
namespace Backend.Stock.Prologue
open D0

def source (name : String) (c : Configuration) (runs : List Clif.RunCommand) : Clif.Function :=
  { D0.source name c runs with blocks := [
      { id := 0, params := [(0, valueType c)], body := [{inst := .nop}],
        term := .jump {block := 1, args := []} },
      { id := 1, body := [{inst := .nop}], term := .ret [0] }] }

def eligible (f : Clif.Function) : Bool :=
  decide (f = source f.name .systemVI64 f.runs)
end Backend.Stock.Prologue
