import FV.Backend.Lowering.StockParameterLoopCfg
import FV.Backend.Proof.StockParameterCheckedWitness

/-! The loop parameter class contains the forward parameter class, and it selects a `while`
loop from Cranelift's filetests that the forward class rejects (#140, T7b-1). -/

namespace Backend.Stock.ParameterLoopCfg
set_option autoImplicit false

private theorem target_nonentry_of_after {f : Clif.Function} {bi : Nat} {bc : Clif.BlockCall}
    (checked : ParameterCfg.targetAfter f bi bc = true) : targetNonentry f bc = true := by
  simp only [ParameterCfg.targetAfter] at checked
  simp only [targetNonentry]
  cases target : f.blocks.findIdx? (·.id == bc.block) with
  | none => simp only [target] at checked; cases checked
  | some ti =>
    simp only [target,decide_eq_true_eq] at checked ⊢
    omega

private theorem control_leaf_of_parameter {f : Clif.Function} {bi : Nat} {term : Clif.Terminator}
    (checked : ParameterCfg.controlLeafEligible f bi term = true) : controlLeafEligible f bi term = true := by
  cases term <;>
    simp only [ParameterCfg.controlLeafEligible,ParameterCfg.controlEligible,controlLeafEligible,
      controlEligible,Bool.and_eq_true] at checked ⊢
  case jump bc => exact target_nonentry_of_after checked
  case brif c yes no =>
    obtain ⟨⟨⟨⟨parameter,yesEmpty⟩,noEmpty⟩,yesGood⟩,noGood⟩ := checked
    exact ⟨⟨⟨⟨parameter,yesEmpty⟩,noEmpty⟩,target_nonentry_of_after yesGood⟩,target_nonentry_of_after noGood⟩
  all_goals exact checked

/-- Every function of the forward parameter class is in the loop class. -/
theorem sourceOk_of_parameter {f : Clif.Function} (checked : ParameterCfg.sourceOk f = true) :
    sourceOk f = true := by
  simp only [ParameterCfg.sourceOk,ParameterCfg.sourceLeafEligible,sourceOk,sourceLeafEligible,
    Bool.and_eq_true] at checked ⊢
  obtain ⟨⟨⟨⟨⟨⟨controls,bodies⟩,params⟩,returns⟩,scope⟩,dominated⟩,abi⟩ := checked
  refine ⟨⟨⟨⟨⟨⟨?_,bodies⟩,params⟩,returns⟩,scope⟩,dominated⟩,abi⟩
  exact List.all_eq_true.mpr fun pair member => control_leaf_of_parameter (List.all_eq_true.mp controls pair member)

namespace Probe

/-- The inclusion applies to the checked returning fixture of the forward class. -/
theorem sourceOk_of_parameter_witness : sourceOk Proof.ParameterCfg.Fixture.function = true := by
  obtain ⟨result,_,_,checked,_⟩ := Proof.ParameterCfg.Fixture.checked_returning_witness
  simp only [ParameterCfg.check,Bool.and_eq_true] at checked
  exact sourceOk_of_parameter checked.1

/-- `%f0` of `cranelift/filetests/filetests/inline/control-flow.clif`: block 1 is the loop
header, block 2 the loop body with the back edge `jump block1(v6, v8)`, block 3 the exit. -/
def whileLoop : Clif.Function := {
  name := "f0"
  sig := { params := [⟨.i32,.none,.normal⟩,⟨.i32,.none,.normal⟩], returns := [⟨.i32,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i32),(1,.i32)], body := [⟨[2],.iconst .i32 0⟩], term := .jump ⟨1,[2,2]⟩ },
    { id := 1, params := [(3,.i32),(4,.i32)], body := [⟨[5],.icmp .eq .i32 1 4⟩],
      term := .brif 4 ⟨3,[]⟩ ⟨2,[]⟩ },
    { id := 2, params := [],
      body := [⟨[6],.binary .iadd .i32 3 0⟩,⟨[7],.iconst .i32 1⟩,⟨[8],.binary .iadd .i32 4 7⟩],
      term := .jump ⟨1,[6,8]⟩ },
    { id := 3, params := [], body := [], term := .ret [3] }] }

/-- The forward class rejects the back edge from block 2 to block 1. -/
theorem forward_rejects_while_loop : ParameterCfg.sourceOk whileLoop = false := by decide

/-- The loop class, with scope, dominance and ABI checks, selects the `while` loop. -/
-- witness: native_decide (the fixed function's selector, scope, dominance and ABI checks only)
theorem selects_while_loop : sourceOk whileLoop = true := by native_decide

end Probe
end Backend.Stock.ParameterLoopCfg
