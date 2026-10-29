module

public import FV.Backend.Lowering.StockParameterCfg
public import FV.Backend.Lowering.StockConditionalRankedCfg
public import FV.Backend.Lowering.StockTwoBlock
public import FV.Backend.Lowering.StockLinearCfg
import FV.Backend.Lowering.StockConditionalCfg
import FV.Backend.Lowering.StockForwardCfg
public import FV.Backend.Lowering.StockTwoBlockEntry
public import FV.Backend.ABIReadCfg
import FV.Backend.StockArithmeticCheck
import FV.Backend.ABIReadOnly
public import FV.Backend.StockMixedCheck
public import FV.Backend.StockLogicalCheck
public import FV.Backend.StockScalarCheck
import FV.Backend.ABIReadFlags
import FV.Backend.ABIReadScalar
import FV.Backend.ABIReadDiv

@[expose] public section

namespace Backend.SemanticNI
set_option autoImplicit false

/-- Keep the legacy lowering verdict, or validate actual Stock provenance and
its finite ABI read boundary. No proof object is supplied by the input. -/
def check (f : Clif.Function) (vc : VCode) : Bool :=
  Proof.Driver.lowerCheck f vc ||
    ((Stock.Arithmetic.check f vc && ABIReadOnly.check f.sig vc) ||
      (Stock.Mixed.check f vc && ABIReadFlags.check f.sig vc) ||
      (Stock.Logical.check f vc && ABIReadFlags.check f.sig vc) ||
      (Stock.Scalar.check f vc && (ABIReadScalar.check f.sig vc || ABIReadDiv.check f.sig vc)) ||
      (Stock.TwoBlock.check f vc && ABIReadCfg.check f.sig vc) ||
      (Stock.TwoBlock.Entry.check f vc && ABIReadCfg.check f.sig vc) ||
      (Stock.LinearCfg.check f vc && ABIReadCfg.check f.sig vc) ||
      (Stock.ForwardCfg.check f vc && ABIReadCfg.check f.sig vc) ||
      (Stock.ConditionalCfg.check f vc && ABIReadCfg.check f.sig vc) ||
      (Stock.ConditionalCfg.rankedCheck f vc && ABIReadCfg.check f.sig vc) ||
      (Stock.ParameterCfg.check f vc && ABIReadCfg.check f.sig vc))

end Backend.SemanticNI
