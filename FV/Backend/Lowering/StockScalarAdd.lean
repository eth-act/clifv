import FV.Backend.Lowering.StockD0

/-! Input syntax of the next complete scalar arithmetic class. The production
entrypoints keep their current selector until the full proof packet is ready. -/
set_option autoImplicit false
namespace Backend.Stock.ScalarAdd
open D0

def source (name : String) (c : Configuration) (runs : List Clif.RunCommand) : Clif.Function :=
  let ty := valueType c
  let signature : Clif.Signature := {
    params := [⟨ty,.none,.normal⟩,⟨ty,.none,.normal⟩]
    returns := [⟨ty,.none,.normal⟩]
    callConv := convention c }
  let block : Clif.Block := {
    id := 0
    params := [(0,ty),(1,ty)]
    body := [⟨[2],.binary .iadd ty 0 1⟩]
    term := .ret [2] }
  {D0.source name c runs with sig := signature, blocks := [block]}

def eligible (f : Clif.Function) : Bool :=
  configurations.any fun c => decide (f = source f.name c f.runs)
end Backend.Stock.ScalarAdd
