import FV.E2E.StockShiftFixtures
namespace E2E.StockCastNIWitness
open Backend.Stock.D0
set_option autoImplicit false

/-- Keep the high sign-extension bits observable in the final source result. -/
def extraBody (config : Configuration) : List Clif.Stmt :=
  if valueType config == .i64 then
    [⟨[54],.ireduce .i32 1⟩,⟨[55],.extend .uextend .i64 54⟩,
     ⟨[56],.extend .sextend .i64 54⟩,⟨[57],.binary .bxor .i64 55 56⟩,
     ⟨[58],.iconst .i32 32⟩,⟨[59],.binary .ushr .i64 57 58⟩,
     ⟨[60],.binary .bxor .i64 59 53⟩]
  else
    [⟨[54],.extend .uextend .i64 1⟩,⟨[55],.extend .sextend .i64 1⟩,
     ⟨[56],.binary .bxor .i64 54 55⟩,⟨[57],.iconst .i32 32⟩,
     ⟨[58],.binary .ushr .i64 56 57⟩,⟨[59],.ireduce .i32 58⟩,
     ⟨[60],.binary .bxor .i32 59 53⟩]

def function (config : Configuration) : Clif.Function :=
  let old := StockShiftNIWitness.function config
  {old with name := "stock_cast_ni", blocks := old.blocks.map fun b =>
    {b with body := b.body ++ extraBody config, term := .ret [60]}}

def resultValue (config : Configuration) (input : Nat → BitVec (valueType config).width) :
    BitVec (valueType config).width :=
  let low := (input 1).setWidth 32
  let signs := ((low.zeroExtend 64 ^^^ low.signExtend 64) >>> 32).setWidth (valueType config).width
  signs ^^^ StockShiftNIWitness.resultValue config input
end E2E.StockCastNIWitness
