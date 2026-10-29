module

public import FV.Backend.Production
public import FV.E2E.ProductionPipeline

@[expose] public section

set_option autoImplicit false
namespace FVTest.StockProductionRuntime
open Backend E2E.LinkCheck

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def input : String :=
  "function %prologue_any_name(i64) -> i64 system_v {\nblock0(v0: i64):\n    nop\n    jump block1\nblock1:\n    nop\n    return v0\n}\n" ++
  "function %retained_d0(i32) -> i32 fast {\nblock0(v0: i32):\n    return v0\n}\n" ++
  "function %legacy_constant() -> i64 {\nblock0:\n    v0 = iconst.i64 7\n    return v0\n}\n"

def check : IO Unit := do
  let pf := Clif.parseFile input
  require (pf.funcs.length == 3 && hasStockPrologue pf) "production fixture source parse/selection failed"
  let prologue ← match pf.funcs.head? with
    | some p => match p.func with
      | .ok f => pure f
      | .error _ => throw (IO.userError "invalid prologue")
    | none => throw (IO.userError "empty fixture")
  for cleanup in [false,true] do
    let old ← compileFileWith Allocator.spill.run pf [] cleanup
    require (old.unsupported.isEmpty && old.funcs.length == 3) "legacy baseline failed"
    let seen ← IO.mkRef false
    let production ← compileFileProduction (fun vcs => do
      for vc in vcs do
        if vc.name == "prologue_any_name" then
          let f := prologue
          match Stock.Production.lower f, lowerFunction f with
          | .ok stock, .ok legacy =>
            require (!(stock.rulesFired == legacy.rulesFired)) "actual Stock history collapsed to legacy"
            require (vc.rulesFired == stock.rulesFired) "compiler allocator received legacy history"
            seen.set true
          | _, _ => throw (IO.userError "actual/legacy lowering fixture failed")
      Allocator.spill.run vcs) pf [] cleanup
    require (← seen.get) "Stock code did not reach production allocator"
    require (production.unsupported.isEmpty && production.funcs.length == 3 &&
      production.unverified.isEmpty && production.unvalidated.isEmpty)
      "production lost mixed-file success or verified stages"
    require (production.text == old.text) "proved prologue changed instruction assembly"
    let calls ← IO.mkRef (0 : Nat)
    let retried ← compileFileProduction (fun vcs => do
      let n ← calls.get
      calls.set (n+1)
      if n == 0 then pure (vcs.map fun _ => .error "forced first-attempt allocator failure")
      else Allocator.spill.run vcs) pf [] cleanup
    require ((← calls.get) == 2) "failed complete attempt did not retry exactly once"
    require (retried.text == old.text && retried.rules == old.rules &&
      retried.unsupported == old.unsupported && retried.unverified == old.unverified &&
      retried.unvalidated == old.unvalidated) "legacy retry changed retained result/stages"
    let fi : FnInput := {clif := input, ra := "null", k := 0, j := 1}
    let I : LinkInput := {funcs := [fi], addrs := [("prologue_any_name",4096)], syms := [], raStar := 8192, D := 4096}
    let fallback := {I with fallback := true}
    require ((fallback.pipeProduction cleanup fi).isOk) "checked allocator spill fallback failed"
  IO.println "Stock production: actual history, mixed D0/legacy functions, both cleanup modes and transactional allocator retry passed"
end FVTest.StockProductionRuntime

def main : IO Unit := FVTest.StockProductionRuntime.check
