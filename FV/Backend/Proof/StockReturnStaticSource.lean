import FV.Backend.Proof.SpillArity
import FV.Backend.Proof.StockReturnStatic
import FV.Backend.Proof.StockReturnSourceWitness
namespace Backend.Stock.Proof.ReturnStaticFixture
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower

def sourceCase (implicit : Bool) : ReturnFixture.Case := ⟨implicit,.i64,by simp [Clif.Ty.width],fun _ => rfl⟩
def function (implicit : Bool) : Clif.Function := ReturnFixture.function (sourceCase implicit)
def expected (implicit : Bool) : MInst := .rets ((ReturnFixture.registers (sourceCase implicit)).zip (ReturnFixture.pins (sourceCase implicit)))
/-- Both ordinary two-result and implicit x8-return sources retain original
scope, dominance, ABI and source arity conditions. -/
theorem source_conditions (implicit : Bool) :
    LowerScope (function implicit) ∧ Dominated (function implicit) ∧ ArityOk (function implicit) ∧ sigAbiOk (function implicit).sig = true := by
  obtain ⟨result,lowered,scope,dominated,abi,entered,source,execution⟩ :=
    ReturnSourceWitness.stock_return_vcode_contract_witness (sourceCase implicit) 0 0
  refine ⟨scope,dominated,?_,abi⟩
  cases implicit <;> apply arityOk_of <;> decide +kernel
end Backend.Stock.Proof.ReturnStaticFixture
