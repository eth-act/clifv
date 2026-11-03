import FV.Backend.Lowering.StockGeneralLoopCfg7NI
import FV.Backend.Proof.StockGeneralLoopWitness6

open Backend
namespace General7Runtime

def identity : Clif.Function := {
  name := "identity"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [{ id := 0, params := [(0,.i64)], body := [], term := .ret [0] }] }

def outputEq (a b : Except String VCode) : Bool :=
  match a,b with
  | .ok x,.ok y => decide (x = y)
  | .error x,.error y => x == y
  | _,_ => false

def selected : Bool :=
  let f := Stock.GeneralLoopCfg6.Fixture.jumptable
  match Stock.lower f with
  | .error _ => false
  | .ok result =>
    outputEq (Stock.GeneralLoopCfg7.NI.lowerValidated f) (.ok result.code) &&
    outputEq (Stock.GeneralLoopCfg7.NI.lowerWithRoutes [(f.name,23)] f) (.ok result.code) &&
    !outputEq (Stock.ParameterArgsCfg.NI.lowerValidated f) (.ok result.code)

def explicitPrevious (f : Clif.Function) : Bool :=
  ((List.range 23) ++ [24,1000]).all fun index =>
    outputEq (Stock.GeneralLoopCfg7.NI.lowerWithRoutes [(f.name,index)] f)
      (Stock.ParameterArgsCfg.NI.lowerWithRoutes [(f.name,index)] f)

def priorIdentity : Bool :=
  match Stock.ParameterArgsCfg.NI.lowerValidated identity with
  | .error _ => false
  | .ok code => outputEq (Stock.GeneralLoopCfg7.NI.lowerValidated identity) (.ok code)

end General7Runtime

def main : IO Unit := do
  let cases := [
    ("new_default_and_route23_actual_stock", General7Runtime.selected),
    ("all_old_routes_and_out_of_range_jumptable", General7Runtime.explicitPrevious Backend.Stock.GeneralLoopCfg6.Fixture.jumptable),
    ("all_old_routes_and_out_of_range_identity", General7Runtime.explicitPrevious General7Runtime.identity),
    ("previous_identity_exact_default", General7Runtime.priorIdentity)]
  for (name, passed) in cases do
    IO.println s!"{name}: {passed}"
  unless cases.all (fun item => item.2) do
    throw (IO.userError "General7 runtime regression")
