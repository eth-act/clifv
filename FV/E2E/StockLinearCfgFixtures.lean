import FV.E2E.StockEntryCfgFixtures

namespace E2E.StockLinearCfgNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Existing operation/first-trap cases now execute in a middle block that
inherits the nine ABI values across an empty-argument entry jump. -/
def functions (config : Configuration) : List (Clif.Function × Clif.Ty) :=
  let broad := (StockEntryCfgNIWitness.scalarFunctions config).map fun (f,ty) =>
    ({f with blocks := [
      {f.blocks[0]! with body := [⟨[],.nop⟩],term := .jump ⟨20,[]⟩},
      {id := 20,params := [],body := f.blocks[0]!.body,term := f.blocks[0]!.term},
      f.blocks[1]!] },ty)
  let direct := ([.i8,.i16,.i32,.i64] : List Clif.Ty).map fun ty =>
    let old := StockCfgNIWitness.function config ty 0
    ({old with blocks := [
      {old.blocks[0]! with body := [⟨[],.nop⟩],term := .jump ⟨20,[]⟩},
      {id := 20,params := [],body := [⟨[],.nop⟩,⟨[200],.iconst ty 0⟩,
        ⟨[100],.binary .rotl ty 1 8⟩],term := .jump ⟨10,[]⟩},
      {id := 10,params := [],body := [⟨[],.nop⟩],term := .ret [100]}]},ty)
  (broad ++ direct).zipIdx.map fun ((f,ty),i) => ({f with name := s!"stock_cfglinear_{i}"},ty)

end E2E.StockLinearCfgNIWitness
