import FV.E2E.StockConditionalForwardCfgFixtures

namespace E2E.StockParameterCfgNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Move the former entry condition into a genuine later block. Fresh entry
parameters pass through actual nonempty jump copies; original values and tails
remain intact, including inherited values, joins and first/later traps. -/
def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  (StockConditionalForwardCfgNIWitness.functions config).zipIdx.map fun ((f,ty),i) =>
    let entry := f.blocks[0]!
    let freshBlock := ((f.blocks.map (·.id)).foldl max 0)+1
    let freshValue := ((f.blocks.flatMap fun b => b.params.map (·.1) ++ b.body.flatMap (·.results)).foldl max 0)+1
    let params := entry.params.zipIdx.map fun ((_,t),j) => (freshValue+j,t)
    let first : Clif.Block := {id := entry.id,params,term := .jump ⟨freshBlock,params.map (·.1)⟩}
    ({f with
      name := s!"stock_cfgparameter_{i}"
      blocks := first :: {entry with id := freshBlock} :: f.blocks.drop 1},ty)

end E2E.StockParameterCfgNIWitness
