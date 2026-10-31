import FV.Backend.StockMemoryCheck

namespace Backend.Stock.MemoryExtending
open Backend.Proof.Driver
set_option autoImplicit false

def extending : Clif.LoadOp → Bool
  | .load => false
  | _ => true

/-- Original syntax identifies extending loads; the previous provider keeps plain loads. -/
def eligible (f : Clif.Function) : Bool :=
  match f.blocks with
  | [b] => match b.body with
    | [⟨[z],.load op ty flags x 0⟩] => match b.term with
      | .ret [ret] => extending op &&
          (z == ret && (b.params.map (·.1)).contains x && flags.trapCode.isNone)
      | _ => false
    | _ => false
  | _ => false

def sourceOk (f : Clif.Function) : Bool :=
  eligible f && lowerScopeB f && dominatedB f && sigAbiOk f.sig &&
    !(sigRets f.sig).any (·.purpose == .sret) && Memory.registerEntry f.sig

def check (f : Clif.Function) (vc : VCode) : Bool :=
  sourceOk f && match Stock.lower f with
  | .error _ => false
  | .ok result => decide (result.code = vc) && Memory.effectsOnly vc

end Backend.Stock.MemoryExtending
