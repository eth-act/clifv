import FVTest.Backend.Lowering.StockArithmeticRuntime

set_option autoImplicit false
namespace FVTest.StockArithmeticCommittedRoute
open _root_.Backend

private def require (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

/-- The positive production path must commit its actual Stock attempt. The
existing runtime gate separately checks the real oracle and forced retry path. -/
def checkAllocator (label : String)
    (allocateBatch : Array VCode → IO (Array (Except String AFunc))) : IO Unit := do
  for config in Stock.D0.configurations do
    let f := E2E.StockArithmeticNIWitness.function config
    let raw ← match Stock.Arithmetic.lowerValidated f with
      | .ok vc => pure vc
      | .error message => throw (IO.userError message)
    require (!Backend.Proof.Driver.lowerCheck f raw && SemanticNI.check f raw)
      "positive fixture did not select actual raw Stock"
    let pf := Clif.parseFile (FVTest.StockArithmeticRuntime.input config)
    let parsed ← match pf.funcs.find? (fun p => p.name == f.name) with
      | none => throw (IO.userError "positive parsed arithmetic source missing")
      | some p => match p.func with
        | .error message => throw (IO.userError s!"positive arithmetic parse failed: {repr message}")
        | .ok parsed => pure parsed
    let selected ← match lowerCheckedArithmeticNI parsed true with
      | .error message => throw (IO.userError message)
      | .ok vc => pure vc
    require (Stock.Arithmetic.eligible parsed && SemanticNI.check parsed raw &&
      !Backend.Proof.Driver.lowerCheck parsed raw && decide (selected = raw))
      "positive parsed source did not select and validate the actual raw Stock branch"
    for cleanup in [false,true] do
      let expected ← match prepare (Stock.Arithmetic.stage cleanup raw) with
        | .ok vc => pure vc
        | .error message => throw (IO.userError message)
      let calls ← IO.mkRef (0 : Nat)
      let seen ← IO.mkRef false
      let production ← compileFileArithmeticNIWhen true (fun vcs => do
        calls.modify (· + 1)
        for vc in vcs do
          if vc.name == f.name then
            require (decide (vc = expected)) "positive compiler did not allocate actual Stock code"
            seen.set true
        allocateBatch vcs) pf [] cleanup
      require ((← calls.get) == 1) "positive Stock attempt silently retried the retained compiler"
      require (← seen.get) "positive Stock function did not reach allocation"
      require (production.funcs.length == 5 && production.unsupported.isEmpty &&
        production.unverified.isEmpty && production.unvalidated.isEmpty && production.layout.isOk)
        "positive Stock attempt did not finish all emitted artifacts and validation stages"
      IO.println s!"Stock arithmetic committed {label} {repr config} cleanup={cleanup} passed"

def check : IO Unit := do
  checkAllocator "lean" (fun vcs => pure (allocateLean vcs))
  checkAllocator "regalloc2" (Allocator.regalloc2 "rust/target/release/lean-regalloc").run

end FVTest.StockArithmeticCommittedRoute

#eval FVTest.StockArithmeticCommittedRoute.check
