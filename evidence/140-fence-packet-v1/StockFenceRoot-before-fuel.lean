import FV.Backend.Proof.StockFenceHelpers
import FV.Backend.Proof.IselAtomic

namespace Backend.Stock.Proof
open Backend.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
attribute [local irreducible] Isle.Aarch64.program

/-- The actual fence RHS emits one fence and changes no scheduling field. -/
theorem stock_fence_rhs_exact (ctx : Ctx) {cfg : Config}
    (overlap : cfg.checkOverlap = false) {n : Nat} (enough : 1000 ≤ n)
    {env : Isle.Interp.Env V} {st next : State} {tr trace : Array RuleId} {out : V}
    (run : (evalExpr program (Stock.sem ctx) cfg n rule_lower_2476.rhs env).run
      (st,tr) = .ok (some out,next,trace)) :
    out = .regsVec [] ∧ next = {st with base := st.base.emit .fence} := by
  have transfer := FenceHelpers.fence_rhs_transfer ctx overlap n env st tr
  have frame := transfer.2 _ _ _ run
  have legacy := transfer.1
  rw [run] at legacy
  simp only [projectResult] at legacy
  have original := legacy.symm
  mem_inv data_program [] at original
  have hF := ‹ApplyInternal _ _ _ _ 46 466 _ _ _ _›
  have hSE := ‹ApplyInternal _ _ _ _ 25 243 _ _ _ _›
  obtain ⟨rfl, first⟩ := fence_helper_ok data_program overlap (by omega) hF
  obtain ⟨mi, decoded, final, output⟩ := side_effect_inst_ok data_program overlap (ctx := ctx) (by omega) hSE
  have fence : MInst.ofV (.data 58 44 []) = some .fence := rfl
  rw [fence,Option.some.injEq] at decoded
  subst mi
  simp only at first final
  rw [first] at final
  exact ⟨output,frame.trans (by rw [final])⟩

end Backend.Stock.Proof
