import FV.Backend.StockVoidCallCheck
import FV.Backend.ABIReadOnly

namespace Backend.Stock.VoidCall.NI
set_option autoImplicit false

def instruction (sig : Clif.Signature) (b k : Nat) (i : MInst) : Bool :=
  match i with
  | .call _ => true
  | _ => Backend.ABIReadOnly.instruction sig b k i

/-- This predicate checks only the finite read boundary. Calls require the
source and retained-record facts that `VoidCall.check` supplies in `NI.check`. -/
def codeCheck (sig : Clif.Signature) (vc : VCode) : Bool :=
  vc.blocks.toList.zipIdx.all fun (block,b) =>
    block.insts.toList.zipIdx.all fun (i,k) => instruction sig b k i

def check (f : Clif.Function) (vc : VCode) : Bool :=
  Stock.VoidCall.check f vc && codeCheck f.sig vc

end Backend.Stock.VoidCall.NI
