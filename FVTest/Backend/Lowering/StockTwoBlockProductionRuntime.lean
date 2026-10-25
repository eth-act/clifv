import FVTest.Backend.Lowering.StockScalarTestSupport
import FV.Backend.TwoBlockNIProduction
import FV.Backend.LinearScan
import FV.E2E.StockCfgFixtures
import FV.Clif.Print

set_option autoImplicit false
namespace FVTest.StockTwoBlockProductionRuntime
open _root_.Backend Backend.Proof.Driver E2E.StockCfgNIWitness
open E2E.StockNarrowNIWitness (caseInput frame)

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- Native symbol names are independent of pretty-printed opcode names. -/
def functions (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  E2E.StockCfgNIWitness.functions config

def input (config : Stock.D0.Configuration) : String :=
  String.join ((functions config).map fun (f,_) => f.print ++ "\n")

/-- Retain the fixed witness samples and add width/truncation/condition boundaries. -/
private def nativeInput (ty : Clif.Ty) (sample : Nat) : Nat → BitVec ty.width :=
  if sample == 9 then fun i => BitVec.ofNat ty.width (if i == 1 then 2^(ty.width-1) else if i == 8 then 2^ty.width-1 else i)
  else if sample < 3 then caseInput ty sample
  else fun i =>
    let boundaries : List Nat := [0,1,2^(ty.width-1)-1,2^(ty.width-1),2^ty.width-1,256,ty.width,ty.width+1]
    BitVec.ofNat ty.width boundaries[(i+sample) % 8]!

private def executionCases (config : Stock.D0.Configuration) : IO Lean.Json := do
  let mut rows := #[]
  for (f,ty) in functions config do
    for sample in List.range 10 do
      let values := nativeInput ty sample
      let args := (List.range 9).map fun i => (values i).toInt
      let outcome := Clif.runLoop Clif.Env.empty {funcs := []} ((f.blocks.map (·.body.length)).sum+f.blocks.length+1)
        ⟨frame f ty values 4096,[],Clif.Mem.empty⟩
      let expected ← match outcome with
        | .returned [value] _ => pure (Lean.toJson value.toInt)
        | .trapped .intDivz => pure (Lean.toJson "int_divz")
        | .trapped .intOvf => pure (Lean.toJson "int_ovf")
        | _ => throw (IO.userError s!"incomplete source outcome: {f.name}, sample {sample}")
      rows := rows.push (Lean.Json.arr #[Lean.toJson f.name,Lean.toJson args,expected])
  pure (Lean.Json.arr rows)

private def checkConfiguration (label : String)
    (allocateBatch : Array VCode → IO (Array (Except String AFunc)))
    (config : Stock.D0.Configuration) : IO Unit := do
  let source := input config
  let pf := Clif.parseFile source
  require (pf.funcs.length == 12) "cfg fixture parse/count failed"
  let excluded := Clif.parseFile (FVTest.StockScalarFixture.legacySource "retained_legacy_cfg")
  let legacy ← match excluded.funcs.head?.bind (·.func.toOption) with
    | some f => pure f
    | none => throw (IO.userError "legacy control did not parse")
  require (!Stock.TwoBlock.eligible legacy) "nonquiet entry escaped the new class"
  let old ← match Stock.Scalar.lowerValidated legacy with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  let retained ← match Stock.TwoBlock.lowerValidated legacy with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  require (decide (retained = old)) "previous complete route changed"
  for parsed in pf.funcs do
    let f ← match parsed.func with
      | .ok f => pure f
      | .error message => throw (IO.userError s!"{repr message}")
    let selected ← match Stock.lower f with
      | .ok result => do
        require (!(result.edgeArgs.all (fun row => row.all (·.isEmpty)))) "CFG fixture lost its nonempty argument copy"
        pure result.code
      | .error message => throw (IO.userError message)
    let observed ← match Stock.TwoBlock.lowerValidated f with
      | .ok vc => pure vc
      | .error message => throw (IO.userError message)
    require (Stock.TwoBlock.sourceOk f && Stock.TwoBlock.check f selected &&
      SemanticNI.check f selected && decide (selected = observed))
      s!"cfg fixture fell back from actual Stock: {f.name}"
  let cases ← executionCases config
  for cleanup in [false,true] do
    let seen ← IO.mkRef (0 : Nat)
    let production ← compileFileTwoBlockNIWhen true (fun vcs => do
      for vc in vcs do
        let some parsed := pf.funcs.find? (fun p => p.name == vc.name)
          | throw (IO.userError "allocator received unknown cfg source")
        let f ← match parsed.func with
          | .ok f => pure f
          | .error message => throw (IO.userError s!"{repr message}")
        let selected ← match Stock.lower f with
          | .ok result => pure result.code
          | .error message => throw (IO.userError message)
        let expected ← match prepare (Stock.Arithmetic.stage cleanup selected) with
          | .ok prepared => pure prepared
          | .error message => throw (IO.userError message)
        require (decide (vc = expected)) s!"allocator did not receive raw Stock: {f.name}"
        seen.modify (· + 1)
      allocateBatch vcs) pf [] cleanup
    require ((← seen.get) == 12 && production.funcs.length == 12 &&
      production.unsupported.isEmpty && production.unverified.isEmpty && production.unvalidated.isEmpty)
      "cfg production lost a successful verified stage"
    if let some directory ← IO.getEnv "STOCK_CFG_NATIVE_OUT" then
      let dir := System.FilePath.mk directory
      IO.FS.createDirAll dir
      let stem := s!"{label}-{repr config}-{if cleanup then "cleanup" else "plain"}"
      let bytes ← match production.object with
        | .ok bytes => pure bytes
        | .error message => throw (IO.userError message)
      IO.FS.writeBinFile (dir / (stem ++ ".o")) bytes
      IO.FS.writeFile (dir / (stem ++ ".json")) production.tableJson
      IO.FS.writeFile (dir / (stem ++ ".clif")) ("test run\ntarget aarch64\n\n" ++ source)
      IO.FS.writeFile (dir / (stem ++ ".cases.json")) cases.compress
    let previous ← compileFileScalarNIWhen true allocateBatch pf [] cleanup
    let calls ← IO.mkRef (0 : Nat)
    let retried ← compileFileTwoBlockNIWhen true (fun vcs => do
      let n ← calls.get
      calls.set (n+1)
      if n == 0 then pure (vcs.map fun _ => .error "forced complete CFG attempt failure")
      else allocateBatch vcs) pf [] cleanup
    require ((← calls.get) == 2 && retried.text == previous.text && retried.rules == previous.rules &&
      retried.unsupported == previous.unsupported && retried.unverified == previous.unverified &&
      retried.unvalidated == previous.unvalidated) "complete CFG retry changed previous output/history/stages"
  IO.println s!"Stock cfg {label} {repr config}: 12 actual Stock functions, both cleanup modes passed"

/-- Reuse the existing real-oracle/read-back checker and its negative control. -/
def check (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit := do
  for config in Stock.D0.configurations do
    checkConfiguration "lean" (fun vcs => pure (allocateLean vcs)) config
    checkConfiguration "regalloc2" (checkedRegalloc2 "rust/target/release/lean-regalloc") config
  let sample ← match Stock.TwoBlock.lowerValidated (functions .systemVI32)[0]!.1 with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  let missingRejected ← try
    discard <| checkedRegalloc2 "/dev/null/lean-regalloc" #[sample]
    pure false
  catch _ => pure true
  require missingRejected "missing regalloc2 binary silently passed the CFG oracle test"
  IO.println "Stock cfg missing-binary negative control passed"

end FVTest.StockTwoBlockProductionRuntime
