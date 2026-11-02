import FV.Backend.StockMemoryCapturedCopyCheck

namespace Backend.Stock.MemorySretCopy
open Backend.Proof.Driver
set_option autoImplicit false

/-- Select four original memory statements without changing their source positions. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [entry,middle,target] => match entry.term,middle.term,target.term,MemoryCapturedCopy.nonNops middle with
    | .jump ⟨first,[]⟩,.jump ⟨second,[]⟩,.ret [],
        [(⟨[low],.load .load .i64 lf0 base 0⟩,i0),
         (⟨[high],.load .load .i64 lf8 otherBase 8⟩,i8),
         (⟨[],.store .store .i64 sf0 storedLow destination 0⟩,j0),
         (⟨[],.store .store .i64 sf8 storedHigh otherDestination 8⟩,j8)] =>
      first == middle.id && second == target.id && base == otherBase &&
        low == storedLow && high == storedHigh && destination == otherDestination &&
        decide (entry.id ≠ middle.id) && decide (entry.id ≠ target.id) && decide (middle.id ≠ target.id) &&
        decide (i0 < j0) && decide (i8 < j8) &&
        (entry.params.map (·.1)).contains base && (entry.params.map (·.1)).contains destination &&
        lf0.trapCode.isNone && lf8.trapCode.isNone && sf0.trapCode.isNone && sf8.trapCode.isNone &&
        entry.body.all (fun stm => decide (stm.inst = .nop)) &&
        target.body.all (fun stm => decide (stm.inst = .nop))
    | _,_,_,_ => false
  | _ => false

/-- Admission uses original source syntax and the existing ABI conditions. -/
def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig && Memory.registerEntry f.sig

/-- Bind the selected source to the actual Stock artifact and existing effect whitelist. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && MemoryStoreCfg.effectsOnly vc

end Backend.Stock.MemorySretCopy
