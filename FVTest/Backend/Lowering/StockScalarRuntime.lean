import FV.Clif.Print
import FV.Backend.ProductionWith
import FV.Backend.Lowering.StockScalarProduction
import FV.E2E.ProductionPipelineWith

set_option autoImplicit false
namespace FVTest.StockScalarRuntime
open Backend E2E.LinkCheck

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def input (config : Stock.D0.Configuration) : String :=
  (Stock.ScalarAdd.source "scalar_any_name" config []).print ++ "\n" ++
  (Stock.Prologue.source "prologue_any_name" .systemVI64 []).print ++ "\n" ++
  "function %retained_d0(i32) -> i32 fast {\nblock0(v0: i32):\n    return v0\n}\n" ++
  "function %legacy_constant() -> i64 {\nblock0:\n    v0 = iconst.i64 7\n    return v0\n}\n"

private def checkConfiguration (config : Stock.D0.Configuration) : IO Unit := do
  let pf := Clif.parseFile (input config)
  require (pf.funcs.length == 4 && pf.funcs.any (fun p => p.func.toOption.any Stock.ScalarAdd.activationEligible)) "production fixture source parse/selection failed"
  let prologue ← match pf.funcs.head? with
    | some p => match p.func with
      | .ok f => pure f
      | .error _ => throw (IO.userError "invalid prologue")
    | none => throw (IO.userError "empty fixture")
  for cleanup in [false,true] do
    let old ← compileFileWith Allocator.spill.run pf [] cleanup
    require (old.unsupported.isEmpty && old.funcs.length == 4) "legacy baseline failed"
    let seen ← IO.mkRef false
    let production ← compileFileProductionWith Stock.ScalarAdd.lower Stock.ScalarAdd.activationEligible (fun vcs => do
      for vc in vcs do
        if vc.name == "scalar_any_name" then
          let f := prologue
          match Stock.ScalarAdd.lower f, lowerFunction f with
          | .ok stock, .ok legacy =>
            require (!(stock.rulesFired == legacy.rulesFired)) "actual Stock history collapsed to legacy"
            require (vc.rulesFired == stock.rulesFired) "compiler allocator received legacy history"
            seen.set true
          | _, _ => throw (IO.userError "actual/legacy lowering fixture failed")
      Allocator.spill.run vcs) pf [] cleanup
    require (← seen.get) "Stock code did not reach production allocator"
    require (production.unsupported.isEmpty && production.funcs.length == 4 &&
      production.unverified.isEmpty && production.unvalidated.isEmpty)
      "production lost mixed-file success or verified stages"
    require (production.text == old.text) "proved prologue changed instruction assembly"
    let calls ← IO.mkRef (0 : Nat)
    let retried ← compileFileProductionWith Stock.ScalarAdd.lower Stock.ScalarAdd.activationEligible (fun vcs => do
      let n ← calls.get
      calls.set (n+1)
      if n == 0 then pure (vcs.map fun _ => .error "forced first-attempt allocator failure")
      else Allocator.spill.run vcs) pf [] cleanup
    require ((← calls.get) == 2) "failed complete attempt did not retry exactly once"
    require (retried.text == old.text && retried.rules == old.rules &&
      retried.unsupported == old.unsupported && retried.unverified == old.unverified &&
      retried.unvalidated == old.unvalidated) "legacy retry changed retained result/stages"
    let fi : FnInput := {clif := input config, ra := "null", k := 0, j := 1}
    let I : LinkInput := {funcs := [fi], addrs := [("scalar_any_name",4096)], syms := [], raStar := 8192, D := 4096}
    let fallback := {I with fallback := true}
    require ((fallback.pipeProductionWith Stock.ScalarAdd.lower cleanup fi).isOk) "checked allocator spill fallback failed"
  IO.println "Stock scalar production: actual arithmetic history, mixed scalar/prologue/D0/legacy functions, both cleanup modes and transactional allocator retry passed"
def check : IO Unit := do
  for config in Stock.D0.configurations do checkConfiguration config

end FVTest.StockScalarRuntime

def main : IO Unit := FVTest.StockScalarRuntime.check
