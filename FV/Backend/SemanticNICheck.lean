import FV.Backend.StockArithmeticCheck
import FV.Backend.ABIReadOnly
import FV.Backend.StockMixedCheck
import FV.Backend.StockLogicalCheck
import FV.Backend.StockScalarCheck
import FV.Backend.ABIReadFlags

namespace Backend.SemanticNI
set_option autoImplicit false

/-- Keep the legacy lowering verdict, or validate actual Stock provenance and
its finite ABI read boundary. No proof object is supplied by the input. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  Proof.Driver.lowerCheck f vc ||
    ((Stock.Arithmetic.check f vc && ABIReadOnly.check f.sig vc) ||
      (Stock.Mixed.check f vc && ABIReadFlags.check f.sig vc) ||
      (Stock.Logical.check f vc && ABIReadFlags.check f.sig vc) ||
      (Stock.Scalar.check f vc && ABIReadFlags.check f.sig vc))

end Backend.SemanticNI
