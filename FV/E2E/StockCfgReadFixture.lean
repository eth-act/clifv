import FV.Backend.Proof.IselExtern
import FV.Backend.ABIReadCfg
import FV.Backend.Proof.StockInheritedFixture

namespace E2E.StockCfgReadFixture
open Backend Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000
private abbrev function := InheritedWitness.function

section Kernel
/-- Fixed executable check of actual compilation, including a real jump.
This introduces no native emitted-code-shape axiom. -/
private theorem read_checked : (Stock.lower function).toOption.map
    (fun result => Backend.ABIReadCfg.check function.sig result.code) = some true := by
  decide +kernel
end Kernel

/-- The actual fixture compilation passes the jump-capable ABI-read check;
the fixed compiler calculation is checked by the kernel. -/
theorem actual_read_check {result : Stock.Result}
    (run : Stock.lower InheritedWitness.function = .ok result) :
    ABIReadCfg.check InheritedWitness.function.sig result.code = true := by
  have checked := read_checked
  rw [run] at checked
  simpa only [Except.toOption,Option.map_some,Option.some.injEq] using checked

end E2E.StockCfgReadFixture
