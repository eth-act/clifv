import FV.Backend.Lowering.StockVoidCallNI
namespace ResultCallReachabilityProbe
open Backend
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
def signature : Clif.Signature := {
  params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV }
def statement : Clif.Stmt := ⟨[31],.call 0 [7]⟩
def caller : Clif.Function := {
  name := "stock_source_call_result",sig := signature
  externs := [(0,{name := "stock_source_identity",sig := signature,colocated := true})]
  blocks := [{id := 0,params := [(7,.i64)],body := [statement],term := .ret [31]}] }
def callee : Clif.Function := {
  name := "stock_source_identity",sig := signature
  blocks := [{id := 0,params := [(101,.i64)],term := .ret [101]}] }

def view (vc : VCode) : String :=
  reprStr (vc.name,vc.blocks.toList,vc.classes.toList,vc.slotBytes,vc.outgoing,vc.rulesFired.toList)
def observed (f : Clif.Function) : IO Unit := do
  let previous := Stock.VoidCall.NI.lowerValidated f
  let stock := (Stock.lower f).map (·.code)
  let legacy := Backend.lowerFunction f
  IO.println s!"function={f.name} previous_ok={previous.isOk} stock_ok={stock.isOk} legacy_ok={legacy.isOk}"
  IO.println s!"void_source={!(Stock.VoidCall.sourceData? f).isNone} sret_source={Stock.MemorySretCopy.eligible f}"
  match previous,stock,legacy with
  | .ok p,.ok s,.ok l =>
    IO.println s!"previous_matches_stock={view p == view s} previous_matches_legacy={view p == view l} stock_matches_legacy={view s == view l}"
    IO.println s!"previous={view p}"
    IO.println s!"stock={view s}"
  | _,_,_ => IO.println "At least one provider rejected the original function."
#eval do
  observed caller
  observed callee
end ResultCallReachabilityProbe
