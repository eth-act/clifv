import FV.Backend.Lowering.StockPrologue
import FV.Backend.Proof.StockPrologueSource

set_option autoImplicit false
namespace Backend.Stock.Prologue
open D0

/-- The code probe uses exactly the source whose complete execution was checked. -/
theorem systemV_i64_source (name : String) (runs : List Clif.RunCommand) :
    source name .systemVI64 runs = Clif.StockPrologueSource.source name runs := by
  rfl

theorem systemV_i64_source_witness (name : String) (runs : List Clif.RunCommand)
    (word : BitVec 64) (mem : Clif.Mem) :
    ∃ (fr : Clif.Frame) (entered : Clif.Mem),
      Clif.enterFunc (source name .systemVI64 runs)
        [Clif.StockPrologueSource.argument word] mem = .ok (fr, entered) ∧
      Clif.runLoop Clif.Env.empty {funcs := [source name .systemVI64 runs]} 4
          ⟨fr, [], entered⟩ = .returned [Clif.StockPrologueSource.argument word] mem := by
  simpa only [systemV_i64_source] using
    (Clif.StockPrologueSource.complete_source_witness name runs word mem)



end Backend.Stock.Prologue
