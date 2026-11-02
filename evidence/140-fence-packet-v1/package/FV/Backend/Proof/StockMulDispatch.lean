import FV.Backend.Proof.IselCtlRuleIds
import FV.Backend.Proof.StockMulValues
import FV.Backend.Proof.StockRootOpcodeMatch
namespace Backend.Stock.Proof.MulComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem inventory : sourceOpcodeIds 77 = [rule_lower_871.id] := by
  unfold sourceOpcodeIds
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel
/-- The original multiplication opcode and successful actual selection determine
its root internally. Existing selected-root theorem variants remain available. -/
theorem selected_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.binary .imul ty x y))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = rule_lower_871 := by
  obtain ⟨_,data,_⟩ := ScalarMul.stock_mul_data inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [inventory,List.mem_singleton] at member
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem
    (by change rule_lower_871 ∈ program.rulesOf 686; rw [data_program.r686]; decide +kernel) member
end Backend.Stock.Proof.MulComplete
