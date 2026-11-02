import FV.Link.ReturnPinCompileDefs
import FV.Front.Read
import FV.E2E.ProductionBoundaryWitness
import FV.E2E.PreparedReturnPinCallsWitness
open Backend E2E E2E.LinkCheck Lean Link
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def main (args : List String) : IO Unit := do
  let dir : System.FilePath := args[0]!
  let output : System.FilePath := args[1]!
  let (b,exe) ← Front.readBundle dir []
  let .ok S := Front.buildSpec {b with sizes := b.markers.map (fun (n,_) => (n,0))}
    | throw (IO.userError "actual allocator layout")
  let SP := S.placedProductionWith Stock.VoidCall.NI.lowerValidated false
  let I := SP.inputProductionWith Stock.VoidCall.NI.lowerValidated false
  let original := PreparedReturnPinCallsWitness.input.funcs
  let .ok A := Front.assemble b | throw (IO.userError "assemble")
  unless A.funcs.map (·.func) == original.map (·.func) do
    throw (IO.userError "original functions or settings changed")
  let initial : LinkSpec := {
    funcs := original
    names := []
    sizes := []
    outside := []
    symNames := original.map (fun fi => fi.func.name)
    R := 0x200160 }
  let old := initial.placedProductionWith Stock.VoidCall.NI.lowerValidated false
  let .ok invalid := Ld.assemble (ProductionBoundaryWitness.plan old)
    | throw (IO.userError "original placeholder reconstruction")
  let valid ← IO.FS.readBinFile exe
  unless !symsOkB I invalid.write && symsOkB I valid do
    throw (IO.userError "expected invalid and valid symbol layouts")
  IO.FS.writeBinFile output invalid.write
  IO.println s!"original-functions-and-settings-exact=true; old-addresses={old.addrs}; actual-addresses={SP.addrs}; invalid-symbol-layout=false; actual-symbol-layout=true"
