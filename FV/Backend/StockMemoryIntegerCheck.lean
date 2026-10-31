import FV.Backend.StockMemoryCheck

namespace Backend.Stock.MemoryUnsigned
open Backend.Proof.Driver
set_option autoImplicit false

/-- Additional source widths preserve the existing i32 provider and its routes. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => match b.body with
    | [⟨[z],.load .load ty flags x 0⟩] => match b.term with
      | .ret [ret] => (ty == .i8 || ty == .i16 || ty == .i64) &&
          (z == ret && (b.params.map (·.1)).contains x && flags.trapCode.isNone)
      | _ => false
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

/-- Bind the source class to its actual Stock artifact and existing effect check. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && Memory.effectsOnly vc

end Backend.Stock.MemoryUnsigned
