import FV.Backend.VoidCallABIProduction

namespace Backend.ReturnPinProfileFile
set_option autoImplicit false

def checked (lower : Clif.Function → Except String VCode)
    (accept : Clif.Function → VCode → Bool) (failure : String)
    (f : Clif.Function) (verify : Bool) : Except String VCode := do
  let raw ← lower f
  if verify && !accept f raw then throw failure
  pure raw

def stage (lower : Clif.Function → Except String VCode)
    (accept : Clif.Function → VCode → Bool) (failure : String)
    (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (checked lower accept failure f verify).map (Stock.Arithmetic.stage cleanup)

def entry (lower : Clif.Function → Except String VCode)
    (accept : Clif.Function → VCode → Bool) (failure : String)
    (f : Clif.Function) (verify cleanup : Bool) : Except String ReturnPinFile.Entry := do
  let raw ← checked lower accept failure f verify
  let prepared ← prepare (Stock.Arithmetic.stage cleanup raw)
  pure ⟨f,raw,prepared,Thunk.mk (fun _ => ReturnPinCheck.pins f raw),rfl⟩

def entries (lower : Clif.Function → Except String VCode)
    (accept : Clif.Function → VCode → Bool) (failure : String)
    (pf : Clif.ParsedFile) (pre : List (String × String)) (cleanup : Bool) :
    Except String (List ReturnPinFile.Entry) :=
  pf.funcs.mapM fun parsed => do
    let f ← parsed.func.mapError (fun error => error.toString)
    let verify := ((unverifiedReason? f).isSome || (pre.lookup parsed.name).isSome ||
      (overBudget? f).isSome).not
    entry lower accept failure f verify cleanup

/-- Compatibility follows from every actual raw artifact and its prepared call metadata. -/
def modeB (lower : Clif.Function → Except String VCode)
    (accept : Clif.Function → VCode → Bool) (failure : String)
    (pf : Clif.ParsedFile) (pre : List (String × String)) (cleanup : Bool) : Bool :=
  (entries lower accept failure pf pre cleanup).toOption.any fun actual =>
    actual.all (fun e => accept e.source e.raw) && ReturnPinFile.check actual

/-- Rejection runs the entire previous file action with its original callback and settings. -/
def compileFileWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (relevant : Clif.Function → Bool) (lower : Clif.Function → Except String VCode)
    (accept : Clif.Function → VCode → Bool) (failure : String)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool) (previous : m FileAsm) : m FileAsm :=
  if !enabled then previous
  else if !(pf.funcs.any fun parsed => parsed.func.toOption.any relevant) ||
      !modeB lower accept failure pf pre cleanup then previous
  else do
    let attempt ← compileFileWithLowering (stage lower accept failure) VCode.rulesFired
      alloc pf pre cleanup
    finishFileVoidCallABI attempt previous

theorem compileFileWhen_disabled {m : Type → Type} [Monad m]
    (relevant : Clif.Function → Bool) (lower : Clif.Function → Except String VCode)
    (accept : Clif.Function → VCode → Bool) (failure : String)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool) (previous : m FileAsm) :
    compileFileWhen false relevant lower accept failure alloc pf pre cleanup previous = previous := by
  simp only [compileFileWhen,Bool.not_false,ite_true]

theorem compileFileWhen_retry {m : Type → Type} [Monad m]
    (relevant : Clif.Function → Bool) (lower : Clif.Function → Except String VCode)
    (accept : Clif.Function → VCode → Bool) (failure : String)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (pre : List (String × String)) (cleanup : Bool) (previous : m FileAsm)
    (rejected : modeB lower accept failure pf pre cleanup = false) :
    compileFileWhen true relevant lower accept failure alloc pf pre cleanup previous = previous := by
  simp only [compileFileWhen,Bool.not_true,Bool.false_eq_true,ite_false,rejected,
    Bool.not_false,Bool.or_true,ite_true]

end Backend.ReturnPinProfileFile
