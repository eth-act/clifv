import FV.Backend.Proof.StockMemoryCapturedCopyCheck
import FV.Backend.Proof.StockMemoryLoadedPointerFixture

namespace Backend.Stock.Memory.CapturedCopy.Fixture
open Backend.Stock.Proof
open IntegerRoots.LoadedPointerFixture (function)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

private def observed : Option Bool :=
  (Stock.lower function).toOption.map fun result => MemoryCapturedCopy.check function result.code
private theorem observed_true : observed = some true := by native_decide

/-- The unchanged original capture inhabits the source class, actual artifact check and complete contract. -/
theorem complete_checked_captured_copy_witness :
    ∃ result : Stock.Result,Stock.lower function = .ok result ∧
      MemoryCapturedCopy.check function result.code = true ∧ CfgClass function ∧ Domain function := by
  have actual := observed_true
  unfold observed at actual
  cases run : Stock.lower function with
  | error message => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at actual
    obtain ⟨lowered,family,_,_,_⟩ := MemoryCapturedCopy.check_sound actual
    exact ⟨result,rfl,actual,family,family.domain⟩

end Backend.Stock.Memory.CapturedCopy.Fixture
