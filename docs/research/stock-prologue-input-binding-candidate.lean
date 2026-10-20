import FV.Backend.Lowering.StockD0
import StockPrologueSourceProbe

namespace Backend.Stock.PrologueProbe
open D0

def source (name : String) (c : Configuration) (runs : List Clif.RunCommand) : Clif.Function :=
  { D0.source name c runs with blocks := [
      { id := 0, params := [(0, valueType c)], body := [{inst := .nop}],
        term := .jump {block := 1, args := []} },
      { id := 1, body := [{inst := .nop}], term := .ret [0] }] }

/-- The code probe uses exactly the source whose complete execution was checked. -/
theorem systemV_i64_source (name : String) (runs : List Clif.RunCommand) :
    source name .systemVI64 runs = Clif.StockPrologueSourceProbe.source name runs := by
  rfl

theorem systemV_i64_source_witness (name : String) (runs : List Clif.RunCommand)
    (word : BitVec 64) (mem : Clif.Mem) :
    ∃ (fr : Clif.Frame) (entered : Clif.Mem),
      Clif.enterFunc (source name .systemVI64 runs)
        [Clif.StockPrologueSourceProbe.argument word] mem = .ok (fr, entered) ∧
      Clif.runLoop Clif.Env.empty {funcs := [source name .systemVI64 runs]} 4
          ⟨fr, [], entered⟩ = .returned [Clif.StockPrologueSourceProbe.argument word] mem := by
  simpa only [systemV_i64_source] using
    (Clif.StockPrologueSourceProbe.complete_source_witness name runs word mem)

#print axioms systemV_i64_source
#print axioms systemV_i64_source_witness


end Backend.Stock.PrologueProbe
