import FV.Backend.MixedNIProduction
import FV.Backend.LinearScan
import FV.E2E.StockArithmeticNIWitness
import FV.E2E.StockMixedWitness
import FV.Clif.Print

set_option autoImplicit false
namespace FVTest.StockMixedRuntime
open _root_.Backend

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def input (config : Stock.D0.Configuration) : String :=
  (E2E.StockMixedNIWitness.function config).print ++ "\n" ++
  ({E2E.StockArithmeticNIWitness.function config with name := "retained_arithmetic"}).print ++ "\n" ++
  (Stock.ScalarAdd.source "retained_scalar" config []).print ++ "\n" ++
  (Stock.Prologue.source "retained_prologue" .systemVI64 []).print ++ "\n" ++
  (Stock.D0.source "retained_d0" .fastI32 []).print ++ "\n" ++
  "function %retained_legacy() -> i64 {\nblock0:\n    v0 = iconst.i64 7\n    return v0\n}\n"

private def checkConfiguration (label : String)
    (allocateBatch : Array VCode → IO (Array (Except String AFunc)))
    (config : Stock.D0.Configuration) : IO Unit := do
  let pf := Clif.parseFile (input config)
  require (pf.funcs.length == 6) "arithmetic fixture parse failed"
  let f := E2E.StockMixedNIWitness.function config
  let raw ← match Stock.Mixed.lowerValidated f with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  require (!Backend.Proof.Driver.lowerCheck f raw && SemanticNI.check f raw)
    "actual mixed output did not enter the paired semantic route"
  for cleanup in [false,true] do
    let retained ← compileFileArithmeticNIWhen true allocateBatch pf [] cleanup
    require (retained.unsupported.isEmpty && retained.funcs.length == 6) "retained baseline failed"
    let expected ← match prepare (Stock.Arithmetic.stage cleanup raw) with
      | .ok vc => pure vc
      | .error message => throw (IO.userError message)
    let seen ← IO.mkRef false
    let production ← compileFileMixedNIWhen true (fun vcs => do
      for vc in vcs do
        if vc.name == f.name then
          require (decide (vc = expected)) "allocator did not receive actual prepared Stock code"
          seen.set true
        else
          let some parsed := pf.funcs.find? (fun p => p.name == vc.name)
            | throw (IO.userError "retained source missing")
          let previous ← match parsed.func with
            | .error message => throw (IO.userError s!"{repr message}")
            | .ok old => match Stock.Arithmetic.lowerValidated old with
              | .error message => throw (IO.userError message)
              | .ok lowered => match prepare (Stock.Arithmetic.stage cleanup lowered) with
                | .error message => throw (IO.userError message)
                | .ok prepared => pure prepared
          require (decide (vc = previous)) "a previously shipped class changed code or metadata"
      allocateBatch vcs) pf [] cleanup
    require (← seen.get) "actual raw Stock did not reach the allocator"
    require (production.funcs.length == 6 && production.unsupported.isEmpty &&
      production.unverified.isEmpty && production.unvalidated.isEmpty)
      "mixed arithmetic/retained functions lost a successful verified stage"
    let calls ← IO.mkRef (0 : Nat)
    let retried ← compileFileMixedNIWhen true (fun vcs => do
      let n ← calls.get
      calls.set (n+1)
      if n == 0 then pure (vcs.map fun _ => .error "forced complete-attempt failure")
      else allocateBatch vcs) pf [] cleanup
    require ((← calls.get) == 2) "complete arithmetic attempt did not retry exactly once"
    require (retried.text == retained.text && retried.rules == retained.rules &&
      retried.unsupported == retained.unsupported && retried.unverified == retained.unverified &&
      retried.unvalidated == retained.unvalidated) "retry changed retained output/history/stages"
  IO.println s!"Stock mixed {label} {repr config}: raw output, stack/unused arguments, mixed retained classes and both cleanup retries passed"

def check : IO Unit := do
  for config in Stock.D0.configurations do
    checkConfiguration "lean" (fun vcs => pure (allocateLean vcs)) config
  let regalloc := (Allocator.regalloc2 "rust/target/release/lean-regalloc").run
  for config in Stock.D0.configurations do
    checkConfiguration "regalloc2" regalloc config

end FVTest.StockMixedRuntime

def main : IO Unit := FVTest.StockMixedRuntime.check
