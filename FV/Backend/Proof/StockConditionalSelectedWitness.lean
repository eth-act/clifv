import FV.Backend.Proof.StockConditionalSelectedAt
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

/-! Non-vacuity of the critical-edge case: the entry branches to a block that jumps to the merge
block, and directly to the merge block with a block argument. The direct edge is critical, so
Stock lowers it as an edge node; the derived lemma shows that its argument is demanded after the
entry body. -/

namespace Backend.Stock.Proof.ConditionalValues.EdgeFixture
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The entry doubles its parameter and branches on it; the false side passes the sum directly to
the merge block, the true side jumps there with the parameter. -/
def function : Clif.Function := {
  name := "conditional_critical_args"
  sig := { params := [⟨.i64,.none,.normal⟩], returns := [⟨.i64,.none,.normal⟩] }
  blocks := [
    { id := 0, params := [(0,.i64)], body := [⟨[1],.binary .iadd .i64 0 0⟩],
      term := .brif 0 ⟨1,[]⟩ ⟨2,[1]⟩ },
    { id := 1, params := [], body := [], term := .jump ⟨2,[0]⟩ },
    { id := 2, params := [(2,.i64)], body := [], term := .ret [2] }] }

private def checks : Bool :=
  lowerScopeB function && dominatedB function &&
  function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) &&
  match Stock.lower function with
  | .error _ => false
  | .ok result => result.order.nodes.contains (.edge 0 1 2) && (result.ctx.defInst? 0).isNone

-- witness: native_decide (the fixed function's input checks, lowering and block order only)
private theorem checks_true : checks = true := by native_decide

theorem critical_edge_argument_demanded (X : ExtSem) :
    ∃ result,∃ (spec : ConditionalBodySpec function result function.blocks[0]! 0 0 0
      ⟨1,[]⟩ ⟨2,[1]⟩ (csem (fun _ => False) ⟨0,0⟩ X) (fun _ _ _ => True) Clif.Env.empty {funcs := []}),
      Stock.lower function = .ok result ∧ Node.edge 0 1 2 ∈ result.order.nodes ∧
      Demanded spec.term.output.state 1 := by
  have h := checks_true
  unfold checks at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨scopeOk,dominatedOk⟩,bodies⟩,lowered⟩ := h
  have scope := lowerScope_of scopeOk
  have dominated := dominated_of dominatedOk
  have family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
    intro b member stm present
    exact Stock.Scalar.maskMixedBodyEligible_sound
      (List.all_eq_true.mp (List.all_eq_true.mp bodies b member) stm present)
  cases run : Stock.lower function with
  | error message => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run,Bool.and_eq_true] at lowered
    obtain ⟨edge,parameterOk⟩ := lowered
    have parameter : result.ctx.defInst? 0 = none := Option.isNone_iff_eq_none.mp parameterOk
    have tag := stock_blockOrder_entry (stock_lower_order run) scope.nonempty
    have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
    obtain ⟨spec⟩ := stock_lower_conditional_body_spec run scope dominated family tag
      (b := function.blocks[0]!) rfl (c := 0) (yes := ⟨1,[]⟩) (no := ⟨2,[1]⟩) rfl
      (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X)
      stable Clif.Env.empty {funcs := []}
    exact ⟨result,spec,rfl,Array.contains_iff_mem.mp edge,
      spec.selected_arguments_demanded run scope tag rfl parameter (index := 1) (bc := ⟨2,[1]⟩) rfl
        (List.mem_singleton_self 1)⟩

end Backend.Stock.Proof.ConditionalValues.EdgeFixture
