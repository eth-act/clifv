import FV.Backend.ReturnPinProduction
import FV.Link.ReturnPinCompileDefs
import FV.Front.Read
import FV.E2E.ProductionBoundaryWitness
open Backend E2E E2E.LinkCheck Lean
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def main (args : List String) : IO Unit := do
  let dir : System.FilePath := args[0]!
  let cleanup := args[1]! == "true"
  let (b,exe) ← Front.readBundle dir []
  let .ok S := Front.buildSpec {b with sizes := b.markers.map (fun (n,_) => (n,0))}
    | throw (IO.userError "actual allocator layout")
  let pf := Clif.parseFile (String.join (S.funcs.map (·.clif)))
  unless !returnPinModeB pf [] cleanup do throw (IO.userError "the typed mixed file must retain the previous mode")
  let SP := S.placedProductionWith Stock.MemoryCapturedCopy.lowerValidated cleanup
  let .ok image := Link.Ld.assemble (ProductionBoundaryWitness.plan SP)
    | throw (IO.userError "actual reserved image")
  IO.FS.writeBinFile exe image.write
  IO.FS.writeFile (dir / "actual-layout.json") (toJson SP.addrs).pretty
  IO.println s!"reserved actual layout: {SP.addrs}"
