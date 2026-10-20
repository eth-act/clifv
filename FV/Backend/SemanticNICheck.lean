import FV.Backend.StockArithmeticCheck
import FV.Backend.ABIReadOnly

namespace Backend.SemanticNI
set_option autoImplicit false

/-- Keep the legacy lowering verdict, or validate actual Stock provenance and
its finite ABI read boundary. No proof object is supplied by the input. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  Proof.Driver.lowerCheck f vc || (Stock.Arithmetic.check f vc && ABIReadOnly.check f.sig vc)

end Backend.SemanticNI
