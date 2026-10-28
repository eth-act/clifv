import FVTest.Backend.Lowering.StockScalarTestSupport
import FV.Backend.ScalarNIProduction
import FV.Backend.LinearScan
import FV.E2E.StockHighMulFixtures
import FV.E2E.StockDivFixtures
import FV.E2E.StockMixedDivFixtures
import FVTest.Backend.Lowering.StockMixedDivProductionInput
import FV.Clif.Print

set_option autoImplicit false
namespace FVTest.StockMixedDivProductionRuntime
open _root_.Backend

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- Export the actual Lean-encoded object and original inputs for native
execution tests. Normal runtime checks retain their existing behavior. -/
private def saveNativeArtifacts (label : String) (config : Stock.D0.Configuration)
    (cleanup : Bool) (production : FileAsm) : IO Unit := do
  if let some directory ← IO.getEnv "STOCK_MIXED_DIV_NATIVE_OUT" then
    let dir := System.FilePath.mk directory
    IO.FS.createDirAll dir
    let stem := s!"{label}-{repr config}-{if cleanup then "cleanup" else "plain"}"
    let bytes ← match production.object with
      | .ok bytes => pure bytes
      | .error message => throw (IO.userError message)
    IO.FS.writeBinFile (dir / (stem ++ ".o")) bytes
    IO.FS.writeFile (dir / (stem ++ ".json")) production.tableJson
    IO.FS.writeFile (dir / (stem ++ ".clif")) ("test run\ntarget aarch64\n\n" ++ input config)

private def checkConfiguration (label : String)
    (allocateBatch : Array VCode → IO (Array (Except String AFunc)))
    (config : Stock.D0.Configuration) : IO Unit := do
  let pf := Clif.parseFile (input config)
  require (pf.funcs.length == 29) "division and retained fixture parse failed"
  let f := E2E.StockMixedDivNIWitness.function config .sdiv false
  let raw ← match Stock.Scalar.lowerValidated f with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  require (Stock.Scalar.activationEligible f && Stock.Scalar.check f raw &&
    !Backend.Proof.Driver.lowerCheck f raw && SemanticNI.check f raw)
    "actual mixed output did not enter the paired semantic route"
  for op in E2E.StockDivNIWitness.operations do
    for safe in [false,true] do
      let original := E2E.StockMixedDivNIWitness.function config op safe
      let observed ← match Stock.Scalar.lowerValidated original with
        | .ok vc => pure vc
        | .error message => throw (IO.userError message)
      require (Stock.Scalar.activationEligible original && Stock.Scalar.check original observed &&
        SemanticNI.check original observed && Backend.ABIReadDiv.check original.sig observed)
        "a real quotient/remainder failed the complete source/ABI checker"
      if safe && decide (op = .sdiv) then
        let selected ← match Stock.lower original with
          | .ok result => pure result
          | .error message => throw (IO.userError message)
        let expectedRoot := if Stock.D0.valueType config == .i64 then 790 else 791
        require (selected.schedule.any fun step =>
          decide (step.decision = .emitted) && step.rules.getLast? == some expectedRoot)
          "constant-divisor fixture did not select its actual signed-division root"
  for cleanup in [false,true] do
    let retained ← compileFileLogicalNIWhen true allocateBatch pf [] cleanup
    require (retained.unsupported.isEmpty && retained.funcs.length == 29) "retained baseline failed"
    let expected ← match prepare (Stock.Arithmetic.stageF cleanup f raw) with
      | .ok vc => pure vc
      | .error message => throw (IO.userError message)
    let seen ← IO.mkRef false
    let production ← compileFileScalarNIWhen true (fun vcs => do
      for vc in vcs do
        if vc.name == f.name then
          require (decide (vc = expected)) "allocator did not receive actual prepared Stock code"
          seen.set true
        else
          let some parsed := pf.funcs.find? (fun p => p.name == vc.name)
            | throw (IO.userError "retained source missing")
          let previous ← match parsed.func with
            | .error message => throw (IO.userError s!"{repr message}")
            | .ok old => match Stock.Scalar.lowerValidated old with
              | .error message => throw (IO.userError message)
              | .ok lowered => match prepare (Stock.Arithmetic.stageF cleanup old lowered) with
                | .error message => throw (IO.userError message)
                | .ok prepared => pure prepared
          require (decide (vc = previous)) "a previously shipped class changed code or metadata"
      allocateBatch vcs) pf [] cleanup
    require (← seen.get) "actual raw Stock did not reach the allocator"
    require (production.funcs.length == 29 && production.unsupported.isEmpty &&
      production.unverified.isEmpty && production.unvalidated.isEmpty)
      "mixed arithmetic/retained functions lost a successful verified stage"
    saveNativeArtifacts label config cleanup production
    let calls ← IO.mkRef (0 : Nat)
    let retried ← compileFileScalarNIWhen true (fun vcs => do
      let n ← calls.get
      calls.set (n+1)
      if n == 0 then pure (vcs.map fun _ => .error "forced complete-attempt failure")
      else allocateBatch vcs) pf [] cleanup
    require ((← calls.get) == 2) "complete Stock attempt did not retry exactly once"
    require (retried.text == retained.text && retried.rules == retained.rules &&
      retried.unsupported == retained.unsupported && retried.unverified == retained.unverified &&
      retried.unvalidated == retained.unvalidated) "retry changed retained output/history/stages"
  IO.println s!"Stock mixeddiv {label} {repr config}: raw output, stack/unused arguments, mixed retained classes and both cleanup retries passed"

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
  let sample ← match Stock.Scalar.lowerValidated
      (E2E.StockDivNIWitness.function .systemVI64 .sdiv) with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  let missingRejected ← try
    discard <| checkedRegalloc2 "/dev/null/lean-regalloc" #[sample]
    pure false
  catch _ => pure true
  require missingRejected "missing regalloc2 binary silently passed the oracle test"
  IO.println "Stock mixeddiv missing-binary negative control passed"

end FVTest.StockMixedDivProductionRuntime

def main : IO Unit := FVTest.StockMixedDivProductionRuntime.check
