import FV.Backend.ArithmeticNIProduction
import FV.Backend.LinearScan
import FV.Clif.Print
import FV.E2E.StockProductionFixtures

set_option autoImplicit false
namespace FVTest.StockArithmeticRuntime
open _root_.Backend

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def input (config : Stock.D0.Configuration) : String :=
  (E2E.StockArithmeticNIWitness.function config).print ++ "\n" ++
  (Stock.ScalarAdd.source "retained_scalar" config []).print ++ "\n" ++
  (Stock.Prologue.source "retained_prologue" .systemVI64 []).print ++ "\n" ++
  (Stock.D0.source "retained_d0" .fastI32 []).print ++ "\n" ++
  "function %retained_legacy() -> i64 {\nblock0:\n    v0 = iconst.i64 7\n    return v0\n}\n"

private def checkConfiguration (label : String)
    (allocateBatch : Array VCode → IO (Array (Except String AFunc)))
    (config : Stock.D0.Configuration) : IO Unit := do
  let pf := Clif.parseFile (input config)
  require (pf.funcs.length == 5) "arithmetic fixture parse failed"
  let f := E2E.StockArithmeticNIWitness.function config
  let raw ← match Stock.Arithmetic.lowerValidated f with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  require (!Backend.Proof.Driver.lowerCheck f raw && SemanticNI.check f raw)
    "actual arithmetic output did not enter the paired semantic route"
  for cleanup in [false,true] do
    let retained ← compileFileScalarWhen true allocateBatch pf [] cleanup
    require (retained.unsupported.isEmpty && retained.funcs.length == 5) "retained baseline failed"
    let expected ← match prepare (Stock.Arithmetic.stage cleanup raw) with
      | .ok vc => pure vc
      | .error message => throw (IO.userError message)
    let seen ← IO.mkRef false
    let production ← compileFileArithmeticNIWhen true (fun vcs => do
      for vc in vcs do
        if vc.name == f.name then
          require (decide (vc = expected)) "allocator did not receive actual prepared Stock code"
          seen.set true
        else
          let some parsed := pf.funcs.find? (fun p => p.name == vc.name)
            | throw (IO.userError "retained source missing")
          let previous ← match parsed.func with
            | .error message => throw (IO.userError s!"{repr message}")
            | .ok old => match Stock.ScalarAdd.lower old with
              | .error message => throw (IO.userError message)
              | .ok lowered => match prepare (Stock.Arithmetic.stage cleanup lowered) with
                | .error message => throw (IO.userError message)
                | .ok prepared => pure prepared
          require (decide (vc = previous)) "a previously shipped class changed code or metadata"
      allocateBatch vcs) pf [] cleanup
    require (← seen.get) "actual raw Stock did not reach the allocator"
    require (production.funcs.length == 5 && production.unsupported.isEmpty &&
      production.unverified.isEmpty && production.unvalidated.isEmpty)
      "mixed arithmetic/retained functions lost a successful verified stage"
    let calls ← IO.mkRef (0 : Nat)
    let retried ← compileFileArithmeticNIWhen true (fun vcs => do
      let n ← calls.get
      calls.set (n+1)
      if n == 0 then pure (vcs.map fun _ => .error "forced complete-attempt failure")
      else allocateBatch vcs) pf [] cleanup
    require ((← calls.get) == 2) "complete arithmetic attempt did not retry exactly once"
    require (retried.text == retained.text && retried.rules == retained.rules &&
      retried.unsupported == retained.unsupported && retried.unverified == retained.unverified &&
      retried.unvalidated == retained.unvalidated) "retry changed retained output/history/stages"
  IO.println s!"Stock arithmetic {label} {repr config}: raw output, stack/unused arguments, mixed retained classes and both cleanup retries passed"

/-- Require real accepted oracle answers, then compare them with the production
allocator's output. A missing binary or spill fallback cannot satisfy this test. -/
private def checkedRegalloc2 (bin : String) (vcs : Array VCode) : IO (Array (Except String AFunc)) := do
  let prepared ← vcs.mapM fun vc => match prepareChecked vc with
    | .ok vcp => pure vcp
    | .error message => throw (IO.userError message)
  let answers ← match ← runLeanRegalloc bin aarch64Env prepared with
    | .ok answers => pure answers
    | .error message => throw (IO.userError message)
  require (answers.size == prepared.size) "real regalloc2 answer count differs"
  let mut expected : Array (Except String AFunc) := #[]
  for i in [:prepared.size] do
    let result ← match answers[i]! with
      | .ok result => pure result
      | .error message => throw (IO.userError message)
    let rf ← match result.oracle with
      | .ok rf => pure rf
      | .error message => throw (IO.userError message)
    let vcp := prepared[i]!
    require (decide (result.prepared = vcp) && (checkAlloc vcp rf).isOk)
      "real regalloc2 allocation was not accepted"
    let af ← match lowerRFunc vcp rf with
      | .ok af => pure af
      | .error message => throw (IO.userError message)
    require (emitReady af) "real regalloc2 output required emission fallback"
    expected := expected.push (.ok af)
  let actual ← (Allocator.regalloc2 bin).run vcs
  require (actual.size == expected.size && (actual.zip expected).all (fun (a,b) =>
    match a,b with
    | .ok a,.ok b => a.name == b.name && a.frameSize == b.frameSize &&
        a.blocks == b.blocks && a.slotBase == b.slotBase && a.frame == b.frame
    | _,_ => false)) "production allocator changed the real checked oracle output"
  pure actual


def check : IO Unit := do
  for config in Stock.D0.configurations do
    checkConfiguration "lean" (fun vcs => pure (allocateLean vcs)) config
  let regalloc := checkedRegalloc2 "rust/target/release/lean-regalloc"
  for config in Stock.D0.configurations do
    checkConfiguration "regalloc2" regalloc config
  let sample ← match Stock.Arithmetic.lowerValidated
      (E2E.StockArithmeticNIWitness.function .systemVI64) with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  let missingRejected ← try
    discard <| checkedRegalloc2 "/dev/null/lean-regalloc" #[sample]
    pure false
  catch _ => pure true
  require missingRejected "missing regalloc2 binary silently passed the oracle test"
  IO.println "Stock arithmetic missing-binary negative control passed"

end FVTest.StockArithmeticRuntime

def main : IO Unit := FVTest.StockArithmeticRuntime.check
