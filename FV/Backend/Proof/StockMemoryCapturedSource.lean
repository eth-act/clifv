import FV.Backend.Proof.StockMemoryCapturedFixture
import FV.Backend.Proof.StockSourceEntry

namespace Backend.Stock.Memory.CapturedFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

def initial : Clif.Frame := { LoadFixture.frame with
  func := function
  body := function.blocks[0]!.body
  term := function.blocks[0]!.term }

/-- The original ABI arguments enter the actual captured function. -/
theorem source_entered :
    Clif.enterFunc function [⟨.i64,4096⟩] LoadFixture.heap =
      .ok (initial,LoadFixture.heap) := rfl

/-- Five original source steps cross the jump and read the initialized heap. -/
theorem source_returned :
    Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial,[],LoadFixture.heap⟩ =
      .returned [⟨.i32,2779096485⟩] LoadFixture.heap := rfl

theorem source_entry : SourceEntry function [⟨.i64,4096⟩] initial :=
  SourceEntry.of_enterFunc source_entered

end Backend.Stock.Memory.CapturedFixture
