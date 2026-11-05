import FV.Backend.ScalarNIProduction
import FV.Backend.LinearScan
import FV.E2E.StockNarrowFixtures
import FV.Clif.Print

set_option autoImplicit false
namespace FVTest.StockNarrowProductionRuntime
open _root_.Backend Backend.Proof.Driver E2E.StockNarrowNIWitness

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- Native symbol names are independent of pretty-printed opcode names. -/
def functions (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  let primitives := widths.flatMap fun ty =>
    ((cases ty).filter fun c => !outsideOriginalScope c).map fun c => (function config c,c.inputTy)
  let all := primitives ++ widths.map (fun ty => (mixedFunction config ty,ty))
  all.zipIdx.map fun ((f,ty),i) => ({f with name := s!"stock_narrow_{i}"},ty)

def input (config : Stock.D0.Configuration) : String :=
  String.join ((functions config).map fun (f,_) => f.print ++ "\n")

/-- Retain the fixed witness samples and add width/truncation/condition boundaries. -/
private def nativeInput (ty : Clif.Ty) (sample : Nat) : Nat → BitVec ty.width :=
  if sample < 3 then caseInput ty sample
  else fun i =>
    let boundaries : List Nat := [0,1,2^(ty.width-1)-1,2^(ty.width-1),2^ty.width-1,256,ty.width,ty.width+1]
    BitVec.ofNat ty.width boundaries[(i+sample) % 8]!

private def executionCases (config : Stock.D0.Configuration) : IO Lean.Json := do
  let mut rows := #[]
  for (f,ty) in functions config do
    for sample in List.range 9 do
      let values := nativeInput ty sample
      let args := (List.range 9).map fun i => (values i).toInt
      let outcome := Clif.runLoop Clif.Env.empty {funcs := []} (f.blocks[0]!.body.length+2)
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
  require (pf.funcs.length == 79) "narrow fixture parse/count failed"
  -- Preserve and exercise the original-scope exclusion rather than dropping it silently.
  let excluded := function config ⟨"excluded_bswap8",.i8,.unary .bswap .i8 1⟩
  require (!lowerScopeB excluded && !Stock.Scalar.sourceOk excluded)
    "i8 bswap changed original source scope"
  for parsed in pf.funcs do
    let f ← match parsed.func with
      | .ok f => pure f
      | .error message => throw (IO.userError s!"{repr message}")
    let selected ← match Stock.lower f with
      | .ok result => pure result.code
      | .error message => throw (IO.userError message)
    let observed ← match Stock.Scalar.lowerValidated f with
      | .ok vc => pure vc
      | .error message => throw (IO.userError message)
    require (Stock.Scalar.sourceOk f && Stock.Scalar.check f selected &&
      SemanticNI.check f selected && decide (selected = observed))
      s!"narrow fixture fell back from actual Stock: {f.name}"
  let cases ← executionCases config
  for cleanup in [false,true] do
    let seen ← IO.mkRef (0 : Nat)
    let production ← compileFileScalarNIWhen true (fun vcs => do
      for vc in vcs do
        let some parsed := pf.funcs.find? (fun p => p.name == vc.name)
          | throw (IO.userError "allocator received unknown narrow source")
        let f ← match parsed.func with
          | .ok f => pure f
          | .error message => throw (IO.userError s!"{repr message}")
        let selected ← match Stock.lower f with
          | .ok result => pure result.code
          | .error message => throw (IO.userError message)
        let expected ← match prepare (Stock.Arithmetic.stageF cleanup f selected) with
          | .ok prepared => pure prepared
          | .error message => throw (IO.userError message)
        require (decide (vc = expected)) s!"allocator did not receive raw Stock: {f.name}"
        seen.modify (· + 1)
      allocateBatch vcs) pf [] cleanup
    require ((← seen.get) == 79 && production.funcs.length == 79 &&
      production.unsupported.isEmpty && production.unverified.isEmpty && production.unvalidated.isEmpty)
      "narrow production lost a successful verified stage"
    if let some directory ← IO.getEnv "STOCK_NARROW_NATIVE_OUT" then
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
  IO.println s!"Stock narrow {label} {repr config}: 79 actual Stock functions, both cleanup modes passed"

/-- Reuse the existing real-oracle/read-back checker and its negative control. -/
def check (checkedRegalloc2 : String → Array VCode → IO (Array (Except String AFunc))) : IO Unit := do
  for config in conventions do
    checkConfiguration "lean" (fun vcs => pure (allocateLean vcs)) config
    checkConfiguration "regalloc2" (checkedRegalloc2 "rust/target/release/lean-regalloc") config
  let sample ← match Stock.Scalar.lowerValidated (functions .systemVI32)[0]!.1 with
    | .ok vc => pure vc
    | .error message => throw (IO.userError message)
  let missingRejected ← try
    discard <| checkedRegalloc2 "/dev/null/lean-regalloc" #[sample]
    pure false
  catch _ => pure true
  require missingRejected "missing regalloc2 binary silently passed the narrow oracle test"
  IO.println "Stock narrow missing-binary negative control passed"

end FVTest.StockNarrowProductionRuntime
