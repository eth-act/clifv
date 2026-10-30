import FV.Backend.Lowering.Stock

namespace Backend.Stock.Proof.ConditionalValues.RankedFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

def function : Clif.Function := {
  name := "conditional_ranked_tail"
  sig := {params := [⟨.i64,.none,.normal⟩],returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,.i64)],term := .brif 7 ⟨1,[]⟩ ⟨2,[]⟩},
    {id := 1,body := [⟨[31],.iconst .i64 1⟩],term := .jump ⟨3,[]⟩},
    {id := 2,body := [⟨[47],.iconst .i64 2⟩],term := .ret [47]},
    {id := 3,term := .ret [31]}] }
def initial (n : BitVec 64) : Clif.Frame := {
  func := function,regs := Clif.Regs.empty.set 7 ⟨.i64,n⟩,slots := [],
  body := [],term := .brif 7 ⟨1,[]⟩ ⟨2,[]⟩ }
theorem lower_success : (Stock.lower function).isOk = true := by decide +kernel

end Backend.Stock.Proof.ConditionalValues.RankedFixture
