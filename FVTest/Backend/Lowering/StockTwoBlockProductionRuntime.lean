import FVTest.Backend.Lowering.StockScalarTestSupport
import FV.Backend.TwoBlockEntryNIProduction
import FV.Backend.LinearScan
import FV.E2E.StockCfgFixtures
import FV.E2E.StockEntryCfgFixtures
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

def entryFunctions (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  E2E.StockEntryCfgNIWitness.functions config

private def functionsFor (entry : Bool) (config : Stock.D0.Configuration) :=
  if entry then entryFunctions config else functions config

def input (config : Stock.D0.Configuration) : String :=
  String.join ((functions config).map fun (f,_) => f.print ++ "\n")

/-- Retain the fixed witness samples and add width/truncation/condition boundaries. -/
private def nativeInput (ty : Clif.Ty) (sample : Nat) : Nat → BitVec ty.width :=
  if sample == 9 then fun i => BitVec.ofNat ty.width (if i == 1 then 2^(ty.width-1) else if i == 8 then 2^ty.width-1 else i)
  else if sample < 3 then caseInput ty sample
  else fun i =>
    let boundaries : List Nat := [0,1,2^(ty.width-1)-1,2^(ty.width-1),2^ty.width-1,256,ty.width,ty.width+1]
    BitVec.ofNat ty.width boundaries[(i+sample) % 8]!

private def executionCases (entry : Bool) (config : Stock.D0.Configuration) : IO Lean.Json := do
  let mut rows := #[]
  for (f,ty) in functionsFor entry config do
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

private def checkConfiguration (entry : Bool) (label : String)
    (allocateBatch : Array VCode → IO (Array (Except String AFunc)))
    (config : Stock.D0.Configuration) : IO Unit := do
  let count := if entry then 16 else 12
  let lower := if entry then Stock.TwoBlock.Entry.lowerValidated else Stock.TwoBlock.lowerValidated
  let previousLower := if entry then Stock.TwoBlock.lowerValidated else Stock.Scalar.lowerValidated
  let eligible := if entry then Stock.TwoBlock.Entry.eligible else Stock.TwoBlock.eligible
  let sourceOk := if entry then Stock.TwoBlock.Entry.sourceOk else Stock.TwoBlock.sourceOk
  let classCheck := if entry then Stock.TwoBlock.Entry.check else Stock.TwoBlock.check
  let compile : Bool → (Array VCode → IO (Array (Except String AFunc))) →
      Clif.ParsedFile → List (String × String) → Bool → IO FileAsm :=
    if entry then @compileFileTwoBlockEntryNIWhen IO _ else @compileFileTwoBlockNIWhen IO _
  let previousCompile : Bool → (Array VCode → IO (Array (Except String AFunc))) →
      Clif.ParsedFile → List (String × String) → Bool → IO FileAsm :=
    if entry then @compileFileTwoBlockNIWhen IO _ else @compileFileScalarNIWhen IO _
  let source := String.join ((functionsFor entry config).map fun (f,_) => f.print ++ "\n")
  let pf := Clif.parseFile source
  require (pf.funcs.length == count) "cfg fixture parse/count failed"
  let excluded := Clif.parseFile (FVTest.StockScalarFixture.legacySource "retained_legacy_cfg")
  let legacy ← match excluded.funcs.head?.bind (·.func.toOption) with
    | some f => pure f
    | none => throw (IO.userError "legacy control did not parse")
  require (!eligible legacy) "nonquiet entry escaped the new class"
  let old ← match previousLower legacy with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  let retained ← match lower legacy with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  require (decide (retained = old)) "previous complete route changed"
  for parsed in pf.funcs do
    let f ← match parsed.func with
      | .ok f => pure f
      | .error message => throw (IO.userError s!"{repr message}")
    if entry then
      require (!Stock.TwoBlock.eligible f && eligible f) "entry-division cohort stayed in the previous class"
    let selected ← match Stock.lower f with
      | .ok result => do
        require (!(result.edgeArgs.all (fun row => row.all (·.isEmpty)))) "CFG fixture lost its nonempty argument copy"
        pure result.code
      | .error message => throw (IO.userError message)
    let observed ← match lower f with
      | .ok vc => pure vc
      | .error message => throw (IO.userError message)
    require (sourceOk f && classCheck f selected &&
      SemanticNI.check f selected && decide (selected = observed))
      s!"cfg fixture fell back from actual Stock: {f.name}"
  let cases ← executionCases entry config
  for cleanup in [false,true] do
    let seen ← IO.mkRef (0 : Nat)
    let production ← compile true (fun vcs => do
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
    require ((← seen.get) == count && production.funcs.length == count &&
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
    let previous ← previousCompile true allocateBatch pf [] cleanup
    let calls ← IO.mkRef (0 : Nat)
    let retried ← compile true (fun vcs => do
      let n ← calls.get
      calls.set (n+1)
      if n == 0 then pure (vcs.map fun _ => .error "forced complete CFG attempt failure")
      else allocateBatch vcs) pf [] cleanup
    require ((← calls.get) == 2 && retried.text == previous.text && retried.rules == previous.rules &&
      retried.unsupported == previous.unsupported && retried.unverified == previous.unverified &&
      retried.unvalidated == previous.unvalidated) "complete CFG retry changed previous output/history/stages"
  IO.println s!"Stock {if entry then "cfgentry" else "cfg"} {label} {repr config}: {count} actual Stock functions, both cleanup modes passed"

/-- Reuse the existing real-oracle/read-back checker and its negative control. -/
private def checkClass (entry : Bool) (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit := do
  for config in Stock.D0.configurations do
    checkConfiguration entry "lean" (fun vcs => pure (allocateLean vcs)) config
    checkConfiguration entry "regalloc2" (checkedRegalloc2 "rust/target/release/lean-regalloc") config
  let lower := if entry then Stock.TwoBlock.Entry.lowerValidated else Stock.TwoBlock.lowerValidated
  let sample ← match lower (functionsFor entry .systemVI32)[0]!.1 with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  let missingRejected ← try
    discard <| checkedRegalloc2 "/dev/null/lean-regalloc" #[sample]
    pure false
  catch _ => pure true
  require missingRejected "missing regalloc2 binary silently passed the CFG oracle test"
  IO.println s!"Stock {if entry then "cfgentry" else "cfg"} missing-binary negative control passed"

def check (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass false checkedRegalloc2

def checkEntry (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass true checkedRegalloc2

end FVTest.StockTwoBlockProductionRuntime
