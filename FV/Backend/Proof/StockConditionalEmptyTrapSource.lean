import FV.Backend.Lowering.Stock
import FV.Backend.Proof.PrepareCheck
import FV.Backend.Proof.LowerFix

namespace Backend.Stock.Proof.ConditionalValues.EmptyTrapFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000

def function : Clif.Function := {
  name := "stock_conditional_empty_arguments_trap"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[]⟩ ⟨2,[]⟩},
    {id := 1,body := [⟨[31],.iconst .i64 1⟩],term := .ret [31]},
    {id := 2,body := [⟨[47],.iconst .i64 0⟩,⟨[48],.div .udiv .i64 47 47⟩],term := .ret [48]}] }
def initial : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,0⟩,slots := [],
  body := [],term := .brif 7 ⟨1,[]⟩ ⟨2,[]⟩ }
theorem lower_success : (Stock.lower function).isOk = true := by decide +kernel

end Backend.Stock.Proof.ConditionalValues.EmptyTrapFixture
