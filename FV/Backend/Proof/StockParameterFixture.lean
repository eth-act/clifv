import FV.Backend.Proof.StockForwardSourceOrder
import FV.Backend.Proof.StockConditionalValues

namespace Backend.Stock.Proof.ParameterCfg.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
def function : Clif.Function := {
  name := "jump_then_parameter_conditional"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .jump ⟨1,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .brif 31 ⟨2,[]⟩ ⟨3,[]⟩},
    {id := 2,body := [⟨[47],.iconst .i64 1⟩],term := .ret [47]},
    {id := 3,body := [⟨[59],.iconst .i64 2⟩],term := .ret [59]}] }
def initial (word : BitVec 64) : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,word⟩,slots := [],body := [],term := .jump ⟨1,[7]⟩ }

namespace Trap
def function : Clif.Function := {
  name := "jump_then_parameter_conditional_divzero"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .jump ⟨1,[7]⟩},
    {id := 1,params := [(31,.i64)],term := .brif 31 ⟨2,[]⟩ ⟨3,[]⟩},
    {id := 2,body := [⟨[47],.iconst .i64 1⟩],term := .ret [47]},
    {id := 3,body := [⟨[59],.iconst .i64 0⟩,⟨[60],.div .udiv .i64 59 59⟩],term := .ret [60]}] }
def initial (word : BitVec 64) : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,word⟩,slots := [],body := [],term := .jump ⟨1,[7]⟩ }
end Trap
end Backend.Stock.Proof.ParameterCfg.Fixture
