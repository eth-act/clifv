import FVTest.Backend.Lowering.StockTwoBlockProductionRuntime
import FV.Backend.Proof.StockMemoryCompatibility

namespace FVTest.StockMemoryRetainedRuntime
open Backend
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)
private def get {α : Type} (r : Except String α) : IO α :=
  match r with | .ok value => pure value | .error error => throw (IO.userError error)

def functions (kind : String) (config : Stock.D0.Configuration) : List (Clif.Function × Clif.Ty) :=
  match kind with
  | "parameter" => FVTest.StockTwoBlockProductionRuntime.parameterFunctions config
  | "conditional-forward" => FVTest.StockTwoBlockProductionRuntime.conditionalForwardFunctions config
  | "conditional" => FVTest.StockTwoBlockProductionRuntime.conditionalFunctions config
  | "forward" => FVTest.StockTwoBlockProductionRuntime.forwardFunctions config
  | "linear" => FVTest.StockTwoBlockProductionRuntime.linearFunctions config
  | "scalar-entry" => FVTest.StockTwoBlockProductionRuntime.scalarEntryFunctions config
  | "entry" => FVTest.StockTwoBlockProductionRuntime.entryFunctions config
  | "cfg" => FVTest.StockTwoBlockProductionRuntime.functions config
  | _ => []

def check (kind : String) : IO Unit := do
  let mut cases := 0
  let mut programs := 0
  for config in Stock.D0.configurations do
    let fixtures := functions kind config
    require (!fixtures.isEmpty) "empty retained class"
    let pf := Clif.parseFile (String.join (fixtures.map fun pair => pair.1.print ++ "\n"))
    require (pf.funcs.length == fixtures.length && pf.funcs.all (·.func.isOk)) "retained parse/identity loss"
    if noMemory : (pf.funcs.any fun p => p.func.toOption.any Stock.Memory.eligible) = false then
      for parsed in pf.funcs do
        let f ← match parsed.func with
          | .ok f => pure f
          | .error error => throw (IO.userError s!"{repr error}")
        let old ← get (Stock.ParameterCfg.lowerValidated f)
        let current ← get (Stock.Memory.lowerValidated f)
        require (decide (current = old)) "retained actual lowering or history changed"
        cases := cases+1
      for cleanup in [false,true] do
        let allocate : Array VCode → IO (Array (Except String AFunc)) := fun vcs => pure (allocateLean vcs)
        have compatible := Stock.Memory.previous_file_exact true allocate pf [] cleanup noMemory
        let old ← compileFileParameterCfgNIWhen true allocate pf [] cleanup
        let current ← compileFileMemoryNIWhen true allocate pf [] cleanup
        require (old.funcs.length == fixtures.length && old.unsupported.isEmpty && old.unverified.isEmpty && old.unvalidated.isEmpty)
          "retained original successful stages missing"
        let oldBytes ← get old.object
        let actualBytes ← get current.object
        require (actualBytes == oldBytes && current.tableJson == old.tableJson &&
          current.unsupported == old.unsupported && current.unverified == old.unverified && current.unvalidated == old.unvalidated)
          "retained whole-program output, identities or stages changed"
        programs := programs+1
    else throw (IO.userError "retained class unexpectedly overlaps memory source selector")
  IO.println s!"STOCK_MEMORY_RETAINED_MATRIX_PASS {kind}: {cases} original functions, {programs} whole programs, exact Lean-allocator bytes/history/stages"

end FVTest.StockMemoryRetainedRuntime

def main (args : List String) : IO UInt32 := do
  FVTest.StockMemoryRetainedRuntime.check (args[0]?.getD "")
  pure 0
