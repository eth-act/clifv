import FV.Backend.StockMemoryCheck
import FV.Backend.StockMemorySinkEffects

/-! Executable source selector and artifact check of the sinking load/extension class:
`[y = load.<i8|i16|i32> x; z = uextend|sextend.<i8..i64> y]` (rules 815/824) or
`[y = atomic_load.<i8|i16|i32> x; z = uextend.<i16..i64> y]` (rule 810), then `return z`.
The trap code of the load is not restricted: the class's semantic contract excludes
faulting loads through the `TrapsExplicit` run premise of the production theorems. The
artifact check admits the acquiring load that rule 810 emits (`sinkEffectsOnly`). -/
namespace Backend.Stock.MemorySinkExt
open Backend.Proof.Driver
set_option autoImplicit false

/-- The extending load that a plain load of `ty` followed by `op` amounts to. -/
def kindOf : Clif.ExtendOp → Clif.Ty → Bool
  | .uextend,.i8 | .sextend,.i8 | .uextend,.i16 | .sextend,.i16
  | .uextend,.i32 | .sextend,.i32 => true
  | _,_ => false

/-- Result types that fit in a 64-bit register. -/
def narrowResult : Clif.Ty → Bool
  | .i8 | .i16 | .i32 | .i64 => true
  | _ => false

/-- The pointer of a source load that the class sinks into an extension `op`: a plain
`load` at offset zero (rules 815/824) or an `atomic_load` under a zero extension
(rule 810). -/
def sourcePointer? : Clif.Inst → Clif.ExtendOp → Option Nat
  | .load .load inTy _ x 0,op => if kindOf op inTy then some x else none
  | .atomicLoad inTy _ x,.uextend => if kindOf .uextend inTy then some x else none
  | _,_ => none

/-- Original syntax selects the class, for a plain or an atomic source load, before any
lowering attempt. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => match b.body with
    | [⟨[y],load⟩,⟨[z],.extend op out operand⟩] => match b.term,sourcePointer? load op with
      | .ret [returned],some x => operand == y && returned == z &&
          narrowResult out && (b.params.map (·.1)).contains x
      | _,_ => false
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

/-- Bind the source class to the actual Stock artifact and its sinking-class effects
(loads, acquiring loads, ABI copies and returns). -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && Memory.sinkEffectsOnly vc

end Backend.Stock.MemorySinkExt
