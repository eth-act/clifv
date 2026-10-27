import FV.E2E.StockLinearCfgFixtures

namespace E2E.StockForwardCfgNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Retain all scalar/division/mask source cases and distribute them across
four to eight blocks. Extra jumps inherit the original ABI values directly. -/
def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  (StockLinearCfgNIWitness.functions config).zipIdx.map fun ((f,ty),i) =>
    let count := 1 + i % 5
    let extra := (List.range count).map fun j =>
      ({id := 1000+j,params := [],body := [⟨[],.nop⟩],
        term := .jump ⟨if j+1 < count then 1000+j+1 else f.blocks[1]!.id,[]⟩} : Clif.Block)
    ({f with name := s!"stock_cfgforward_{i}",blocks :=
      {f.blocks[0]! with term := .jump ⟨1000,[]⟩} :: extra ++ f.blocks.drop 1},ty)

end E2E.StockForwardCfgNIWitness
