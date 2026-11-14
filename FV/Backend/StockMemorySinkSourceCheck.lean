import FV.Backend.StockMemorySinkExtCheck
import FV.Backend.StockMemorySinkEffects

/-! Executable source selector and artifact check of the sinking load/extension class for
a plain or an atomic source load: `[y = load.<i8|i16|i32> x; z = uextend|sextend y]` (rules
815/824) or `[y = atomic_load.<i8|i16|i32> x; z = uextend y]` (rule 810), then `return z`.
The artifact check admits the acquiring load that rule 810 emits. Not wired into production
yet; the plain-only `eligible`/`check` stay the production selector. -/
namespace Backend.Stock.MemorySinkExt
open Backend.Proof.Driver
set_option autoImplicit false

/-- The pointer of a source load that the class sinks into an extension `op`: a plain
`load` at offset zero (rules 815/824) or an `atomic_load` under a zero extension
(rule 810). -/
def sourcePointer? : Clif.Inst → Clif.ExtendOp → Option Nat
  | .load .load inTy _ x 0,op => if kindOf op inTy then some x else none
  | .atomicLoad inTy _ x,.uextend => if kindOf .uextend inTy then some x else none
  | _,_ => none

/-- Original syntax selects the class, for a plain or an atomic source load, before any
lowering attempt. -/
def eligibleAny (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => match b.body with
    | [⟨[y],load⟩,⟨[z],.extend op out operand⟩] => match b.term,sourcePointer? load op with
      | .ret [returned],some x => operand == y && returned == z &&
          narrowResult out && (b.params.map (·.1)).contains x
      | _,_ => false
    | _ => false
  | _ => false

def sourceOkAny (f : Clif.Function) : Bool :=
  eligibleAny f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

/-- Bind the source class to the actual Stock artifact and its sinking-class effects
(loads, acquiring loads, ABI copies and returns). -/
def checkAny (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOkAny f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && Memory.sinkEffectsOnly vc

end Backend.Stock.MemorySinkExt
