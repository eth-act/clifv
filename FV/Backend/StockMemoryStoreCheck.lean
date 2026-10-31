import FV.Backend.StockMemoryCheck

namespace Backend.Stock.Memory.Store

/-- Retain the existing effect forms and admit concrete store effects. -/
def effectInstruction : MInst → Bool
  | .store .. => true
  | i => Memory.effectInstruction i

/-- The store consumer checks the actual emitted instructions. -/
def effectsOnly (vc : VCode) : Bool :=
  vc.blocks.toList.all (fun b => b.insts.toList.all effectInstruction)

/-- The previous whitelist remains accepted exactly as before. -/
theorem effectsOnly_of_previous {vc : VCode} (previous : Memory.effectsOnly vc = true) :
    effectsOnly vc = true := by
  apply List.all_eq_true.mpr
  intro b member
  apply List.all_eq_true.mpr
  intro i present
  have before := List.all_eq_true.mp (List.all_eq_true.mp previous b member) i present
  cases i <;> simp_all [effectInstruction,Memory.effectInstruction]

end Backend.Stock.Memory.Store

namespace Backend.Stock.MemoryStore
open Backend.Proof.Driver
set_option autoImplicit false

def scalarParameter : Clif.Ty → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

/-- The first store selector reads only original source syntax. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => match b.body with
    | [⟨[],.store op ty flags value pointer 0⟩] => match b.term with
      | .ret [] => (b.params.map (·.1)).contains pointer &&
          b.params.any (fun q => q.1 == value && scalarParameter q.2) && flags.trapCode.isNone
      | _ => false
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && Memory.Store.effectsOnly vc

end Backend.Stock.MemoryStore
