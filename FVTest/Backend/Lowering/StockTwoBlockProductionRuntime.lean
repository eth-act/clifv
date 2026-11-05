import FV.E2E.StockParameterCfgFixtures
import FV.Backend.ParameterCfgNIProduction
import FV.E2E.StockConditionalForwardCfgFixtures
import FV.Backend.ConditionalForwardCfgNIProduction
import FV.E2E.StockConditionalCfgFixtures
import FV.Backend.ConditionalCfgNIProduction
import FVTest.Backend.Lowering.StockScalarTestSupport
import FV.Backend.ForwardCfgNIProduction
import FV.Backend.LinearScan
import FV.E2E.StockCfgFixtures
import FV.E2E.StockEntryCfgFixtures
import FV.E2E.StockLinearCfgFixtures
import FV.E2E.StockForwardCfgFixtures
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

def scalarEntryFunctions (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  E2E.StockEntryCfgNIWitness.scalarFunctions config

def linearFunctions (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  E2E.StockLinearCfgNIWitness.functions config

def forwardFunctions (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  E2E.StockForwardCfgNIWitness.functions config

def conditionalFunctions (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  E2E.StockConditionalCfgNIWitness.functions config

def conditionalForwardFunctions (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  E2E.StockConditionalForwardCfgNIWitness.functions config

def parameterFunctions (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  E2E.StockParameterCfgNIWitness.functions config

private def functionsFor (entry scalarEntry linear forward : Bool) (config : Stock.D0.Configuration) (conditional : Bool := false) (conditionalForward : Bool := false) (parameter : Bool := false) :=
  if parameter then parameterFunctions config else if conditionalForward then conditionalForwardFunctions config else if conditional then conditionalFunctions config else if forward then forwardFunctions config else if linear then linearFunctions config else if scalarEntry then scalarEntryFunctions config else if entry then entryFunctions config else functions config

def input (config : Stock.D0.Configuration) : String :=
  String.join ((functions config).map fun (f,_) => f.print ++ "\n")

/-- Retain the fixed witness samples and add width/truncation/condition boundaries. -/
private def nativeInput (ty : Clif.Ty) (sample : Nat) : Nat → BitVec ty.width :=
  if sample == 9 then fun i => BitVec.ofNat ty.width (if i == 1 then 2^(ty.width-1) else if i == 8 then 2^ty.width-1 else i)
  else if sample < 3 then caseInput ty sample
  else fun i =>
    let boundaries : List Nat := [0,1,2^(ty.width-1)-1,2^(ty.width-1),2^ty.width-1,256,ty.width,ty.width+1]
    BitVec.ofNat ty.width boundaries[(i+sample) % 8]!

private def executionCases (entry scalarEntry linear forward : Bool) (config : Stock.D0.Configuration) (conditional : Bool := false) (conditionalForward : Bool := false) (parameter : Bool := false) : IO Lean.Json := do
  let mut rows := #[]
  for (f,ty) in functionsFor entry scalarEntry linear forward config conditional conditionalForward parameter do
    for sample in List.range 10 do
      let values := nativeInput ty sample
      let args := (List.range 9).map fun i => (values i).toInt
      let originalFrame := frame f ty values 4096
      let sourceFrame := if parameter then
          {originalFrame with regs := (Clif.Regs.empty.setMany (f.blocks[0]!.params.map (·.1))
            (E2E.StockNarrowNIWitness.arguments ty values)).getD Clif.Regs.empty}
        else originalFrame
      let outcome := Clif.runLoop Clif.Env.empty {funcs := []} ((f.blocks.map (·.body.length)).sum+f.blocks.length+1)
        ⟨sourceFrame,[],Clif.Mem.empty⟩
      let expected ← match outcome with
        | .returned [value] _ => pure (Lean.toJson value.toInt)
        | .trapped .intDivz => pure (Lean.toJson "int_divz")
        | .trapped .intOvf => pure (Lean.toJson "int_ovf")
        | _ => throw (IO.userError s!"incomplete source outcome: {f.name}, sample {sample}")
      rows := rows.push (Lean.Json.arr #[Lean.toJson f.name,Lean.toJson args,expected])
  pure (Lean.Json.arr rows)

private def checkConfiguration (entry scalarEntry linear forward : Bool) (label : String)
    (allocateBatch : Array VCode → IO (Array (Except String AFunc)))
    (config : Stock.D0.Configuration) (conditional : Bool := false) (conditionalForward : Bool := false) (parameter : Bool := false) : IO Unit := do
  let count := if parameter then 100 else if conditionalForward then 100 else if conditional then 100 else if linear then 100 else if scalarEntry then 96 else if entry then 16 else 12
  let lower := if parameter then Stock.ParameterCfg.lowerValidated else if conditionalForward then Stock.ConditionalForwardCfg.lowerValidated else if conditional then Stock.ConditionalCfg.lowerValidated else if forward then Stock.ForwardCfg.lowerValidated else if linear then Stock.LinearCfg.lowerValidated else if entry then Stock.TwoBlock.Entry.lowerValidated else Stock.TwoBlock.lowerValidated
  let previousLower := if parameter then Stock.ConditionalForwardCfg.lowerValidated else if conditionalForward then Stock.ConditionalCfg.lowerValidated else if conditional then Stock.ForwardCfg.lowerValidated else if forward then Stock.LinearCfg.lowerValidated else if linear then Stock.TwoBlock.Entry.lowerValidated else if entry then Stock.TwoBlock.lowerValidated else Stock.Scalar.lowerValidated
  let eligible := if parameter then Stock.ParameterCfg.eligible else if conditionalForward then Stock.ConditionalForwardCfg.eligible else if conditional then Stock.ConditionalCfg.eligible else if forward then Stock.ForwardCfg.eligible else if linear then Stock.LinearCfg.eligible else if entry then Stock.TwoBlock.Entry.eligible else Stock.TwoBlock.eligible
  let sourceOk := if parameter then Stock.ParameterCfg.sourceOk else if conditionalForward then Stock.ConditionalCfg.rankedSourceOk else if conditional then Stock.ConditionalCfg.sourceOk else if forward then Stock.ForwardCfg.sourceOk else if linear then Stock.LinearCfg.sourceOk else if entry then Stock.TwoBlock.Entry.sourceOk else Stock.TwoBlock.sourceOk
  let classCheck := if parameter then Stock.ParameterCfg.check else if conditionalForward then Stock.ConditionalCfg.rankedCheck else if conditional then Stock.ConditionalCfg.check else if forward then Stock.ForwardCfg.check else if linear then Stock.LinearCfg.check else if entry then Stock.TwoBlock.Entry.check else Stock.TwoBlock.check
  let compile : Bool → (Array VCode → IO (Array (Except String AFunc))) →
      Clif.ParsedFile → List (String × String) → Bool → IO FileAsm :=
    if parameter then @compileFileParameterCfgNIWhen IO _ else if conditionalForward then @compileFileConditionalForwardCfgNIWhen IO _ else if conditional then @compileFileConditionalCfgNIWhen IO _ else if forward then @compileFileForwardCfgNIWhen IO _ else if linear then @compileFileLinearCfgNIWhen IO _ else if entry then @compileFileTwoBlockEntryNIWhen IO _ else @compileFileTwoBlockNIWhen IO _
  let previousCompile : Bool → (Array VCode → IO (Array (Except String AFunc))) →
      Clif.ParsedFile → List (String × String) → Bool → IO FileAsm :=
    if parameter then @compileFileConditionalForwardCfgNIWhen IO _ else if conditionalForward then @compileFileConditionalCfgNIWhen IO _ else if conditional then @compileFileForwardCfgNIWhen IO _ else if forward then @compileFileLinearCfgNIWhen IO _ else if linear then @compileFileTwoBlockEntryNIWhen IO _ else if entry then @compileFileTwoBlockNIWhen IO _ else @compileFileScalarNIWhen IO _
  let source := String.join ((functionsFor entry scalarEntry linear forward config conditional conditionalForward parameter).map fun (f,_) => f.print ++ "\n")
  let pf := Clif.parseFile source
  require (pf.funcs.length == count) "cfg fixture parse/count failed"
  let excluded := Clif.parseFile (FVTest.StockScalarFixture.legacySource "retained_legacy_cfg")
  let legacy ← match excluded.funcs.head?.bind (·.func.toOption) with
    | some f => pure f
    | none => throw (IO.userError "legacy control did not parse")
  -- Keep the former multiplying-entry negative control as positive coverage:
  -- it is deliberately part of the broader scalar class now.
  if entry && !linear then
    require (eligible legacy) "existing multiplying entry missed the broader scalar class"
    let raw ← match Stock.lower legacy with
      | .ok result => pure result.code
      | .error message => throw (IO.userError message)
    let selected ← match lower legacy with
      | .ok vc => pure vc
      | .error message => throw (IO.userError message)
    require (decide (selected = raw)) "multiplying entry did not select actual Stock code"
  -- Three source blocks remain outside the proved two-block class and exercise
  -- the same complete previous-route fallback without changing the old input.
  let legacy := if entry then {legacy with blocks := [
    {legacy.blocks[0]! with term := .jump ⟨2,[2]⟩},
    {id := 2,params := [(4,.i64)],body := [],term := .jump ⟨1,[4]⟩},
    legacy.blocks[1]!]} else legacy
  let legacy := if linear then {legacy with blocks := [
    legacy.blocks[0]!,{legacy.blocks[1]! with term := .jump ⟨3,[4]⟩},
    {id := 3,params := [(5,.i64)],body := [],term := .jump ⟨1,[5]⟩},legacy.blocks[2]!]} else legacy
  let legacy := if forward then {legacy with blocks := [legacy.blocks[0]!,legacy.blocks[2]!,legacy.blocks[1]!,legacy.blocks[3]!]} else legacy
  require (!eligible legacy) "out-of-class control escaped the source selector"
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
        let copies := !(result.edgeArgs.all (fun row => row.all (·.isEmpty)))
        let sourceCopies := f.blocks.any fun b => (dests b.term).any fun bc => !bc.args.isEmpty
        require (if parameter then copies == sourceCopies else if conditionalForward then copies == sourceCopies else if conditional then !copies else if linear then copies == sourceCopies else copies) "CFG fixture changed its source edge-copy shape"
        pure result.code
      | .error message => throw (IO.userError message)
    let observed ← match lower f with
      | .ok vc => pure vc
      | .error message => throw (IO.userError message)
    require (sourceOk f && classCheck f selected &&
      SemanticNI.check f selected && decide (selected = observed))
      s!"cfg fixture fell back from actual Stock: {f.name}"
  let cases ← executionCases entry scalarEntry linear forward config conditional conditionalForward parameter
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
        -- Allocation receives staged raw code; the allocator performs checked preparation.
        -- Retain the previous preparation-identity checks for the older cohorts.
        let expected ← if parameter || conditional || conditionalForward then pure (Stock.Arithmetic.stageF cleanup f selected) else match prepare (Stock.Arithmetic.stageF cleanup f selected) with
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
    if parameter || conditionalForward then
      let retainedLeaf := (if parameter then conditionalForwardFunctions config else conditionalFunctions config)[0]!.1
      let added := (if parameter then parameterFunctions config else conditionalForwardFunctions config)[0]!.1
      require ((if parameter then Stock.ConditionalForwardCfg.eligible retainedLeaf else Stock.ConditionalCfg.eligible retainedLeaf) && !eligible retainedLeaf && eligible added)
        "mixed retry control lost the previous conditional class"
      let mixed := Clif.parseFile (retainedLeaf.print ++ "\n" ++ added.print)
      let priorMixed ← previousCompile true allocateBatch mixed [] cleanup
      let attempts ← IO.mkRef (0 : Nat)
      let mixedRetry ← compile true (fun vcs => do
        let n ← attempts.get
        attempts.set (n+1)
        if n == 0 then pure (vcs.map fun _ => .error "forced mixed ranked/leaf failure")
        else allocateBatch vcs) mixed [] cleanup
      require ((← attempts.get) == 2 && mixedRetry.text == priorMixed.text && mixedRetry.rules == priorMixed.rules &&
        mixedRetry.unsupported == priorMixed.unsupported && mixedRetry.unverified == priorMixed.unverified &&
        mixedRetry.unvalidated == priorMixed.unvalidated)
        "ranked retry discarded a successful previous conditional stage"
      let disabled ← compile false allocateBatch mixed [] cleanup
      let priorDisabled ← previousCompile false allocateBatch mixed [] cleanup
      require (disabled.text == priorDisabled.text && disabled.rules == priorDisabled.rules &&
        disabled.unsupported == priorDisabled.unsupported && disabled.unverified == priorDisabled.unverified &&
        disabled.unvalidated == priorDisabled.unvalidated)
        "disabled ranked adapter changed the original pipeline/settings"
  IO.println s!"Stock {if parameter then "cfgparameter" else if conditionalForward then "cfgconditionalforward" else if conditional then "cfgconditional" else if forward then "cfgforward" else if linear then "cfglinear" else if scalarEntry then "cfgscalarentry" else if entry then "cfgentry" else "cfg"} {label} {repr config}: {count} actual Stock functions, both cleanup modes passed"

/-- Reuse the existing real-oracle/read-back checker and its negative control. -/
private def checkClass (entry scalarEntry linear forward : Bool) (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) (conditional : Bool := false) (conditionalForward : Bool := false) (parameter : Bool := false) : IO Unit := do
  for config in Stock.D0.configurations do
    checkConfiguration entry scalarEntry linear forward "lean" (fun vcs => pure (allocateLean vcs)) config conditional conditionalForward parameter
    checkConfiguration entry scalarEntry linear forward "regalloc2" (checkedRegalloc2 "rust/target/release/lean-regalloc") config conditional conditionalForward parameter
  let lower := if parameter then Stock.ParameterCfg.lowerValidated else if conditionalForward then Stock.ConditionalForwardCfg.lowerValidated else if conditional then Stock.ConditionalCfg.lowerValidated else if forward then Stock.ForwardCfg.lowerValidated else if linear then Stock.LinearCfg.lowerValidated else if entry then Stock.TwoBlock.Entry.lowerValidated else Stock.TwoBlock.lowerValidated
  let sample ← match lower (functionsFor entry scalarEntry linear forward .systemVI32 conditional conditionalForward parameter)[0]!.1 with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  let missingRejected ← try
    discard <| checkedRegalloc2 "/dev/null/lean-regalloc" #[sample]
    pure false
  catch _ => pure true
  require missingRejected "missing regalloc2 binary silently passed the CFG oracle test"
  IO.println s!"Stock {if parameter then "cfgparameter" else if conditionalForward then "cfgconditionalforward" else if conditional then "cfgconditional" else if forward then "cfgforward" else if linear then "cfglinear" else if scalarEntry then "cfgscalarentry" else if entry then "cfgentry" else "cfg"} missing-binary negative control passed"

def check (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass false false false false checkedRegalloc2

def checkEntry (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass true false false false checkedRegalloc2

def checkScalarEntry (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass true true false false checkedRegalloc2

def checkLinear (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass true true true false checkedRegalloc2

def checkForward (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass true true true true checkedRegalloc2

def checkConditional (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass false false false false checkedRegalloc2 true

def checkConditionalForward (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass false false false false checkedRegalloc2 false true

def checkParameter (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit :=
  checkClass false false false false checkedRegalloc2 false false true

end FVTest.StockTwoBlockProductionRuntime
