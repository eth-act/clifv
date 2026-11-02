import FV.Backend.MemoryCapturedCopyNIProduction
import FV.Backend.SemanticABICheck
import FV.Backend.Lowering.StockVoidCallNI
import FV.Backend.ReturnPinCheck

namespace Backend
set_option autoImplicit false

def lowerCheckedVoidCallABI (f : Clif.Function) (verify : Bool) : Except String VCode :=
  let attempt := do
    let vc ← Stock.VoidCall.NI.lowerValidated f
    if verify && !SemanticABI.checkCalls f vc then
      throw "lowering rejected by the ABI-aware caller semantic validator"
    pure vc
  match attempt with
  | .ok vc => .ok vc
  | .error _ => lowerCheckedMemoryCapturedCopyNI f verify

def lowerForAllocationVoidCallABI (f : Clif.Function) (verify cleanup : Bool) : Except String VCode :=
  (lowerCheckedVoidCallABI f verify).map (Stock.Arithmetic.stage cleanup)

namespace ReturnPinFile

/-- Preserve every target for indirect calls, including duplicate names. -/
structure Entry where
  source : Clif.Function
  raw : VCode
  prepared : VCode
  pins : Thunk (List Reg)
  pins_eq : pins.get = ReturnPinCheck.pins source raw

def entry (f : Clif.Function) (verify cleanup : Bool) : Except String Entry := do
  let raw ← lowerCheckedVoidCallABI f verify
  let prepared ← prepare (Stock.Arithmetic.stage cleanup raw)
  pure ⟨f,raw,prepared,Thunk.mk (fun _ => ReturnPinCheck.pins f raw),rfl⟩

def Entry.matches (e : Entry) (definitions : List (Reg × Reg)) : Bool :=
  decide ((definitions.map (·.1)).take e.pins.get.length = e.pins.get.take definitions.length)

theorem Entry.matches_eq (e : Entry) (definitions : List (Reg × Reg)) :
    e.matches definitions = ReturnPinCheck.check definitions e.source e.raw := by
  simp only [Entry.matches,e.pins_eq,ReturnPinCheck.check]

structure Context where
  entries : List Entry
  direct : String → Option Entry

def context (entries : List Entry) : Context :=
  let byName : Std.HashMap String Entry := entries.foldr
    (fun e table => table.insert e.source.name e) {}
  ⟨entries,fun name => byName[name]?⟩

theorem context_direct (entries : List Entry) (name : String) :
    (context entries).direct name = entries.find? (fun e => e.source.name == name) := by
  induction entries with
  | nil => simp [context]
  | cons e entries ih =>
    simp only [context,List.foldr_cons,Std.HashMap.getElem?_insert,List.find?_cons] at ih ⊢
    by_cases same : e.source.name = name
    · simp [same]
    · simpa only [show (e.source.name == name) = false from beq_eq_false_iff_ne.mpr same,
        show (name == e.source.name) = false from beq_eq_false_iff_ne.mpr (Ne.symm same),Bool.false_eq_true,if_false] using ih

/-- Unknown indirect targets use the complete local target set before addresses exist. -/
def site (C : Context) (info : CallInfo) : Bool :=
  match info.dest with
  | .sym name => match C.direct name with
    | none => true
    | some e => e.matches info.defs
  | .reg (.vreg _ .int) => C.entries.all fun e =>
    decide (((locsOf e.source.sig).filterMap fun | .reg r => some r | .stack _ => none).length ≠ info.uses.length) || e.matches info.defs
  | _ => true

def instruction (C : Context) : MInst → Bool
  | .call info => site C info
  | .tryCall info _ => site C info
  | _ => true

def check (entries : List Entry) : Bool :=
  let C := context entries
  entries.all fun e => e.prepared.blocks.all fun block => block.insts.all (instruction C)

def entries (pf : Clif.ParsedFile) (preUnverified : List (String × String))
    (cleanup : Bool) : Except String (List Entry) :=
  pf.funcs.mapM fun p => do
    let f ← p.func.mapError (fun error => error.toString)
    let verify := ((unverifiedReason? f).isSome || (preUnverified.lookup p.name).isSome ||
      (overBudget? f).isSome).not
    entry f verify cleanup

end ReturnPinFile

/-- A rejected complete attempt runs the unchanged previous action. -/
def finishFileVoidCallABI {m : Type → Type} [Monad m] (attempt : FileAsm)
    (previous : m FileAsm) : m FileAsm :=
  if !attempt.unsupported.isEmpty || !attempt.layout.isOk then previous else pure attempt

/-- The decision keeps the previous result or a complete, encodable attempt. -/
theorem finishFileVoidCallABI_choice (attempt previous : FileAsm) :
    Id.run (finishFileVoidCallABI attempt (pure previous)) = previous ∨
    (Id.run (finishFileVoidCallABI attempt (pure previous)) = attempt ∧
      attempt.unsupported.isEmpty = true ∧ attempt.layout.isOk = true) := by
  unfold finishFileVoidCallABI
  split
  · exact Or.inl rfl
  · rename_i valid
    exact Or.inr ⟨rfl,by simpa using valid⟩

/-- Retry the complete previous file with its original input and allocation callback. -/
def compileFileVoidCallABIWhen {m : Type → Type} [Monad m] (enabled : Bool)
    (alloc : Array VCode → m (Array (Except String AFunc))) (pf : Clif.ParsedFile)
    (preUnverified : List (String × String) := []) (cleanup : Bool := true) : m FileAsm := do
  if !enabled then return ← compileFileMemoryCapturedCopyNIWhen false alloc pf preUnverified cleanup
  let relevant := pf.funcs.any fun p => p.func.toOption.any fun f =>
    Stock.MemorySretCopy.eligible f || (Stock.VoidCall.sourceData? f).isSome
  if !relevant then return ← compileFileMemoryCapturedCopyNIWhen true alloc pf preUnverified cleanup
  let pins := (ReturnPinFile.entries pf preUnverified cleanup).toOption.any ReturnPinFile.check
  if !pins then return ← compileFileMemoryCapturedCopyNIWhen true alloc pf preUnverified cleanup
  let attempt ← compileFileWithLowering lowerForAllocationVoidCallABI VCode.rulesFired
    alloc pf preUnverified cleanup
  finishFileVoidCallABI attempt (compileFileMemoryCapturedCopyNIWhen true alloc pf preUnverified cleanup)

end Backend
