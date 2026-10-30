import FV.Backend.Proof.StockEdgeCode
import FV.Backend.Proof.StockLinearCfgShape

namespace Backend.Stock.Proof.LinearCfgTrapWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 10000000

/-- Three-block first-trap layout: nops around a division,
empty jump arguments, and a later return reading the middle block's result. -/
def function : Clif.Function := {
  name := "stock_linear_divide"
  sig := {params := [{ty := .i64},{ty := .i64}],returns := [{ty := .i64}]}
  blocks := [
    {id := 0,params := [(0,.i64),(1,.i64)],body := [⟨[],.nop⟩],term := .jump ⟨10,[]⟩},
    {id := 10,params := [],body := [⟨[],.nop⟩,⟨[2],.div .udiv .i64 0 1⟩],term := .jump ⟨20,[]⟩},
    {id := 20,params := [],body := [⟨[],.nop⟩],term := .ret [2]}] }

private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
-- witness: native_decide (fixed original-input dominance only)
private theorem dominated : Dominated function := dominated_of (by native_decide)
private theorem compiled : (Stock.lower function).isOk = true := by decide +kernel

/-- Actual kernel-checked compilation and original source conditions inhabit
all three original nodes; the scan-state coupling is supplied by the real run. -/
theorem actual_linear_driver_witness : ∃ result,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      result.order = ⟨#[.original 0,.original 1,.original 2],#[#[1],#[2],#[]]⟩ := by
  have success := compiled
  cases run : Stock.lower function with
  | error message => rw [run] at success; cases success
  | ok result =>
    refine ⟨result,rfl,scope,dominated,?_⟩
    exact Except.ok.inj ((stock_lower_order run).symm.trans (LinearCfg.block_order_three
      (entry := function.blocks[0]!) (middle := function.blocks[1]!) (target := function.blocks[2]!)
      (first := ⟨10,[]⟩) (second := ⟨20,[]⟩) (xs := [2])
      rfl rfl rfl rfl rfl rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)))

end Backend.Stock.Proof.LinearCfgTrapWitness
