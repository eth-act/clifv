import FV.Backend.Lowering.StockParameterCfg
import FV.Backend.Lowering.StockConditionalRankedCfg
import FV.Backend.Lowering.StockTwoBlock
import FV.Backend.Lowering.StockLinearCfg
import FV.Backend.Lowering.StockConditionalCfg
import FV.Backend.Lowering.StockForwardCfg
import FV.Backend.Lowering.StockTwoBlockEntry
import FV.Backend.ABIReadCfg
import FV.Backend.StockArithmeticCheck
import FV.Backend.ABIReadOnly
import FV.Backend.StockMixedCheck
import FV.Backend.StockLogicalCheck
import FV.Backend.StockScalarCheck
import FV.Backend.StockMemoryCheck
import FV.Backend.StockMemoryCfgCheck
import FV.Backend.StockMemoryIntegerCheck
import FV.Backend.StockMemoryExtLoadCheck
import FV.Backend.ABIReadFlags
import FV.Backend.ABIReadScalar
import FV.Backend.ABIReadDiv

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
      (Stock.ParameterCfg.check f vc && ABIReadCfg.check f.sig vc) || Stock.Memory.check f vc || Stock.MemoryCfg.check f vc || Stock.MemoryUnsigned.check f vc || Stock.MemoryExtending.check f vc)

end Backend.SemanticNI
