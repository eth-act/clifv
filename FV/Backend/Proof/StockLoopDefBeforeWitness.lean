import FV.Backend.Proof.StockLoopDefBefore
import FV.Backend.Proof.StockParameterLoopProbe

/-! Non-vacuity of `stock_lower_defBefore_ssa` (#140, T7b-4) on the `while` loop `%f0` of
`cranelift/filetests/filetests/inline/control-flow.clif` (`ParameterLoopCfg.Probe.whileLoop`), the
fixture of the T7b-3 witness `LoopCarry.Witness.def_carry_witness`.

The T7b-3 witness checks `DefBefore` on the actual lowering with `native_decide`. Here
`while_loop_defBefore` derives it for every successful lowering from the general theorem and the
SSA check (`decide`), without `native_decide`. `while_loop_defBefore_witness` shows that the
lowering succeeds and that `DefBefore` has real instances on it: `v0` (a parameter of the entry
block) is available at the entries of the header (block 1) and the latch (block 2), and `v3` (a
parameter of the header) at the latch's. The `native_decide` there checks only these lowering
and availability facts; `DefBefore` and the consequence that neither loop block inherits its own
definitions come from the general theorems. -/

namespace Backend.Stock.Proof.LoopCarry.DefBeforeWitness
open Backend.Proof Backend.Proof.Driver Backend.Stock.ParameterLoopCfg.Probe
set_option autoImplicit false

private theorem while_loop_ssa : (valueDefs whileLoop).Nodup := by decide

/-- `DefBefore` holds for every successful lowering of the `while` loop (no `native_decide`). -/
theorem while_loop_defBefore {result : Result} (run : Stock.lower whileLoop = .ok result) :
    DefBefore whileLoop result :=
  stock_lower_defBefore_ssa run while_loop_ssa

/-- The facts of the actual lowering of the `while` loop that make `DefBefore` apply: the labels of
blocks 0, 1 and 2, and three values that the loop blocks inherit. -/
def Inherits (result : Result) : Prop :=
  result.order.nodes[0]? = some (.original 0) ∧ result.order.nodes[1]? = some (.original 1) ∧
  result.order.nodes[2]? = some (.original 2) ∧
  0 ∈ (availIn whileLoop result.ctx).getD 1 [] ∧ 0 ∈ (availIn whileLoop result.ctx).getD 2 [] ∧
  3 ∈ (availIn whileLoop result.ctx).getD 2 []

instance (result : Result) : Decidable (Inherits result) := by
  unfold Inherits
  infer_instance

-- witness: native_decide (the fixed function's lowering and availability facts only, not `DefBefore`)
private theorem observed : (Stock.lower whileLoop).toOption.map (fun result => decide (Inherits result)) =
    some true := by
  native_decide

/-- The lowering of the `while` loop succeeds, `DefBefore` holds for it, the loop blocks inherit
`v0` (defined at label 0) and `v3` (defined at label 1), and neither loop block inherits its own
parameters or results. -/
theorem while_loop_defBefore_witness :
    ∃ result : Result,Stock.lower whileLoop = .ok result ∧ DefBefore whileLoop result ∧ Inherits result ∧
      (∀ t ∈ [1,2],∀ x,x ∈ (availIn whileLoop result.ctx).getD t [] →
        x ∉ parsOf whileLoop t ∧ x ∉ defsOf whileLoop t) := by
  have checked := observed
  cases run : Stock.lower whileLoop with
  | error message => rw [run] at checked; cases checked
  | ok result =>
    rw [run] at checked
    have facts : Inherits result := of_decide_eq_true (Option.some.inj checked)
    refine ⟨result,rfl,while_loop_defBefore run,facts,?_⟩
    intro t member x incoming
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact stock_lower_not_inherit_own run while_loop_ssa facts.2.1 incoming
    · exact stock_lower_not_inherit_own run while_loop_ssa facts.2.2.1 incoming

end Backend.Stock.Proof.LoopCarry.DefBeforeWitness
