import FV.Link.ReturnPinExeWith
import FV.Front.Read
open E2E E2E.LinkCheck Backend
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
 def main (args : List String) : IO Unit := do
  let (b,exe) ← Front.readBundle args[0]! []
  let .ok S := Front.buildSpec {b with sizes := b.markers.map (fun (n,_) => (n,0))}
    | throw (IO.userError "spec")
  let SP := S.placedProductionWith Stock.VoidCall.NI.lowerValidated false
  let file ← IO.FS.readBinFile exe
  let I := SP.inputProductionWith Stock.VoidCall.NI.lowerValidated false
  let R := I.resultsProductionWith Stock.VoidCall.NI.lowerValidated false
  IO.println s!"scope {inScopeInPar I}; mode {okRReturnPinCalls (productionStage false) I R}; attempt {Link.ReturnPinCompilerWith.attempt Stock.VoidCall.NI.lowerValidated SP file false |>.toOption.isSome}"
  for e in R do
    IO.println s!"{e.1.name}: {E2E.LinkCheck.chksSemanticFor returnPinCallsExtra (productionStage false) I (progOf R) (tabOf R) e.1 e.2 |>.filter (fun x => !x.2) |>.map (·.1)} pins={returnPinChecks I R e.1}"
  match Link.ReturnPinCompilerWith.attempt Stock.VoidCall.NI.lowerValidated SP file false with
  | .ok _ => IO.println "accepted"
  | .error m => IO.println m
