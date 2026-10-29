module

public import FV.Backend.Proof.StockTwoBlockEntryCheck

@[expose] public section

namespace Backend.Stock.Proof.EntryScalarWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- An entry add feeds an entry division before two real successor copies;
value0 remains inherited even after its local demand ends. -/
def function : Clif.Function := {
  name := "stock_entry_scalar_division_inherited"
  sig := {params := [{ty := .i64},{ty := .i64}],returns := [{ty := .i64}]}
  blocks := [
    {id := 0,params := [(0,.i64),(1,.i64)],body := [⟨[100],.binary .iadd .i64 0 1⟩,⟨[200],.div .udiv .i64 100 1⟩],
      term := .jump ⟨10,[200,100]⟩},
    {id := 10,params := [(101,.i64),(201,.i64)],body := [⟨[102],.binary .iadd .i64 0 101⟩],term := .ret [102]}] }

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
-- witness: native_decide (fixed original-input dominance only; no emitted-code fact)
private theorem dominated : Dominated function := dominated_of (by native_decide)
private theorem compiled : (Stock.lower function).isOk = true := by decide +kernel


/-- Actual compilation and original source checks inhabit the broader checked
class. All fixed calculations, including lowering, are kernel checked. -/
theorem actual_entry_scalar_driver_witness : ∃ result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      Stock.TwoBlock.Entry.eligible function = true ∧ Stock.Scalar.Domain function := by
  have eligible : Stock.TwoBlock.Entry.eligible function = true := by decide +kernel
  have domain := Stock.TwoBlock.Entry.domain_of_eligible eligible scope dominated (by decide +kernel)
  have success := compiled
  cases run : Stock.lower function with
  | error message => rw [run] at success; cases success
  | ok result => exact ⟨result,rfl,scope,dominated,eligible,domain⟩


end Backend.Stock.Proof.EntryScalarWitness
