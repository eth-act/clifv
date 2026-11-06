import FV.Backend.StockMemoryCheck

/-! Executable source selector and artifact check of the sinking load/extension class
`[y = load.<i8|i16|i32> x; z = uextend|sextend.<i8..i64> y]; return z`. The trap code
of the load is not restricted: the class's semantic contract excludes faulting loads
through the `TrapsExplicit` run premise of the production theorems. -/
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

/-- Original syntax selects the class before any lowering attempt. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => match b.body with
    | [⟨[y],.load .load inTy _ x 0⟩,⟨[z],.extend op out operand⟩] => match b.term with
      | .ret [returned] => kindOf op inTy && operand == y && returned == z &&
          narrowResult out && (b.params.map (·.1)).contains x
      | _ => false
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

/-- Bind the source class to the actual Stock artifact and its load-only effects. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && Memory.effectsOnly vc

end Backend.Stock.MemorySinkExt
