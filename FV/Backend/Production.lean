module

public import FV.Backend
public import FV.Backend.Lowering.StockProduction

@[expose] public section

/-! Production rollout orchestration. Both attempts use the original inputs,
verification flags, allocator and emission pipeline. No artifact is published here. -/
set_option autoImplicit false
namespace Backend

def lowerCheckedProduction (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.Production.lower f
    if verify && !Proof.Driver.lowerCheck f vc then
      throw "lowering rejected by the M7 lowering validator (lowerCheck)"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerChecked f verify

def lowerForAllocationProduction (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedProduction f verify).map fun vc => if cleanup then DeadCleanup.prune vc else vc

def hasStockPrologue (pf : Clif.ParsedFile) : Bool :=
  pf.funcs.any fun p => match p.func with
    | .ok f => Stock.Prologue.eligible f
    | .error _ => false

/-- Retry the retained compiler after any failed function or final layout failure.
The retry is delayed until the attempt fails and uses the same allocator/settings. -/
def compileFileProduction {m : Type → Type} [Monad m]
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !hasStockPrologue pf then return ← compileFileWith alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationProduction VCode.rulesFired
    alloc pf preUnverified cleanup
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then
    compileFileWith alloc pf preUnverified cleanup
  else pure attempt

/-- Settings outside the currently proved consumer class retain their entrypoint. -/
def compileFileProductionWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm :=
  if enabled then compileFileProduction alloc pf preUnverified cleanup
  else compileFileWith alloc pf preUnverified cleanup

end Backend
