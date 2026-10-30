import FV.Backend.Lowering.Stock
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Proof.InheritedWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Source value0 is inherited by the second block, rather than passed as a parameter.
The first body emits the constant9, and the full source result is16. -/
def function : Clif.Function := {
  name := "stock_inherited_entry_value"
  sig := {params := [{ty := .i64}],returns := [{ty := .i64}]}
  blocks := [
    {id := 0,params := [(0,.i64)],body := [⟨[1],.iconst .i64 9⟩,⟨[],.nop⟩],term := .jump ⟨10,[1]⟩},
    {id := 10,params := [(2,.i64)],body := [⟨[3],.binary .iadd .i64 0 2⟩],term := .ret [3]}] }

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
-- witness: native_decide (fixed original-input dominance only; no code shape)
private theorem dominated : Dominated function := dominated_of (by native_decide)
private theorem checked : (Stock.lower function).isOk = true := by decide +kernel

/-- Successful actual compilation uses the original source scope/dominance.
Compilation and scope use kernel proofs; only fixed input dominance uses the
permitted native witness check. No emitted-code shape fact is assumed. -/
theorem actual_inherited_driver_witness : ∃ result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function := by
  have success := checked
  cases run : Stock.lower function with
  | error message =>
    rw [run] at success
    change false = true at success
    cases success
  | ok result => exact ⟨result,rfl,scope,dominated⟩

end Backend.Stock.Proof.InheritedWitness
