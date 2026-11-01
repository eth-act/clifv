import FV.Backend.MemorySretCopyABIProduction
import FV.Backend.LinearScan

/-! Actual sret provider, prepared allocator input, object bytes, and complete-file retry. -/
namespace FVTest.StockMemorySretCopyProductionObject
open Backend Backend.Proof.Driver
set_option autoImplicit false

private def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def get {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def originalName : String := "_RNxC7fv_demo11HawPMC3YC2b"
private def variantName : String := "memory_sret_copy_variant"

private def checkOne (out : System.FilePath) (captured : String) (cleanup : Bool) : IO Unit := do
  let functionOnly := String.intercalate "\n" ((captured.splitOn "\n").dropWhile (fun line => !line.startsWith "function "))
  let renamed := functionOnly.replace originalName variantName
  let variant := renamed.replace "nop" "nop\n    nop"
  require (decide (variant ≠ renamed)) "the NOP variant did not add a statement"
  let retained := "function %memory_retained(i64) -> i64 system_v {\nblock0(v0: i64):\n    return v0\n}\n"
  let parsed := Clif.parseFile (captured ++ "\n" ++ variant ++ "\n" ++ retained)
  require (parsed.funcs.length == 3) "the original fixtures lost a function"
  for source in parsed.funcs do
    match source.func with
    | .ok _ => pure ()
    | .error message => throw (IO.userError s!"{source.name}: {repr message}")
  let production ← compileFileMemorySretCopyABIWhen true (fun codes => do
    for code in codes do
      let some source := parsed.funcs.find? (fun p => p.name == code.name)
        | throw (IO.userError "allocator source missing")
      let f ← match source.func with
        | .ok f => pure f
        | .error message => throw (IO.userError s!"{repr message}")
      let raw ← get (Stock.MemorySretCopy.lowerValidated f)
      if f.name == originalName || f.name == variantName then
        require (Stock.MemorySretCopy.check f raw) "the actual sret artifact failed its source check"
        require (SemanticABI.check f raw) "the actual sret artifact failed ABI-aware validation"
        let routed ← get (Stock.MemorySretCopy.lowerWithRoutes [(f.name,20)] f)
        require (decide (routed = raw)) "route20 changed the actual sret artifact"
      let expected ← get (Backend.prepare (Stock.Arithmetic.stage cleanup raw))
      require (decide (code = expected)) "allocator input changed from the actual prepared artifact"
    pure (allocateLean codes)) parsed [] cleanup
  require (production.funcs.length == 3 && production.unsupported.isEmpty &&
    production.unverified.isEmpty && production.unvalidated.isEmpty) "the production adapter lost a verified stage"
  let previous ← compileFileMemoryCapturedCopyNIWhen true (fun codes => pure (allocateLean codes)) parsed [] cleanup
  let attempts ← IO.mkRef (0 : Nat)
  let retried ← compileFileMemorySretCopyABIWhen true (fun codes => do
    let count ← attempts.get
    attempts.set (count+1)
    if count == 0 then pure (codes.map fun _ => .error "forced sret-attempt failure")
    else pure (allocateLean codes)) parsed [] cleanup
  let retryBytes ← get retried.object
  let previousBytes ← get previous.object
  require ((← attempts.get) ≥ 2 && retryBytes.data == previousBytes.data)
    "complete-file retry changed the previous object"
  let disabled ← compileFileMemorySretCopyABIWhen false (fun codes => pure (allocateLean codes)) parsed [] cleanup
  let previousDisabled ← compileFileMemoryCapturedCopyNIWhen false (fun codes => pure (allocateLean codes)) parsed [] cleanup
  let disabledBytes ← get disabled.object
  let previousDisabledBytes ← get previousDisabled.object
  require (disabledBytes.data == previousDisabledBytes.data) "disabled adapter changed the previous object"
  let stem := if cleanup then "sret-cleanup" else "sret-plain"
  IO.FS.writeBinFile (out / (stem ++ ".o")) (← get production.object)
  IO.FS.writeFile (out / (stem ++ ".json")) production.tableJson
  IO.println s!"{stem}: original source, NOP variant, route20, allocator input, stages, and complete-file retry passed"

end FVTest.StockMemorySretCopyProductionObject

def main (args : List String) : IO Unit := do
  let [out,source] := args | throw (IO.userError "usage: sret-object OUT ORIGINAL.clif")
  let path : System.FilePath := out
  IO.FS.createDirAll path
  let captured ← IO.FS.readFile source
  IO.FS.writeFile (path / "original.clif") captured
  for cleanup in [false,true] do
    FVTest.StockMemorySretCopyProductionObject.checkOne path captured cleanup
