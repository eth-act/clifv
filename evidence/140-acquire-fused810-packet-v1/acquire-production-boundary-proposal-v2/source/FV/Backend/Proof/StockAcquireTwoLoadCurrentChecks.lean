import FV.Backend
import FV.Backend.SemanticABICheck
import FV.Backend.Lowering.StockArithmetic

namespace Backend.Stock.Proof.AcquireCurrentChecks
open Backend
set_option autoImplicit false

def originalFunction : Clif.Function := {
  name := "two_deferred_acquires"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    returns := [⟨.i64,.none,.normal⟩,⟨.i64,.none,.normal⟩]
    callConv := some .systemV }
  blocks := [{id := 0,params := [(7,.i64),(31,.i64)],body := [
    ⟨[63],.atomicLoad .i8 {} 7⟩,
    ⟨[64],.atomicLoad .i8 {} 31⟩,
    ⟨[100],.extend .uextend .i64 63⟩,
    ⟨[101],.extend .uextend .i64 64⟩],term := .ret [100,101]}]}

/-- Diagnostic only. This observation does not introduce an acceptance premise. -/
def observeChecks : Except String String := do
  let result ← Stock.lower originalFunction
  pure (reprStr (SemanticNI.check originalFunction result.code,
    SemanticABI.check originalFunction result.code,
    SemanticABI.checkCalls originalFunction result.code,
    Proof.Driver.lowerCheck originalFunction result.code,
    Stock.Arithmetic.eligible originalFunction,
    result.code.rulesFired.toList))

/-- Compare the real default lowering route with the direct Stock result in each mode. -/
def observeDefaultRoute (cleanup : Bool) : Except String String := do
  let result ← Stock.lower originalFunction
  let raw ← vcodeJson result.code
  let chosen ← lowerForAllocation originalFunction
    (verifiable originalFunction || verifiableT originalFunction ||
      verifiableTC originalFunction || verifiableTCF originalFunction) cleanup
  let selected ← vcodeJson chosen
  pure (reprStr (cleanup,raw == selected,chosen.rulesFired.toList)++"\n"++selected)

#eval observeChecks
#eval observeDefaultRoute false
#eval observeDefaultRoute true

end Backend.Stock.Proof.AcquireCurrentChecks
