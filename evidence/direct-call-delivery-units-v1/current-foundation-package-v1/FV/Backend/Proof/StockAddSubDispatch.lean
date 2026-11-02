import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.StockAddSubMatch
namespace Backend.Stock.Proof.ScalarAddSub
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program
private theorem add_inventory : sourceOpcodeIds 73 = [595,597,596,598,590,589,592,591,594,593,588] := by decide +kernel
private theorem sub_inventory : sourceOpcodeIds 74 = [747,748,599,746,749,745] := by decide +kernel
/-- Actual source opcode dispatch includes every scalar add/subtract candidate,
including existing base and fused multiply roots. No chosen rule certificate
or narrower family is substituted for the actual first-match selection. -/
theorem stock_addsub_selected_rule_ids {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (subtract : Bool) {i x y : Nat} {info : IInfo} {ty : Clif.Ty}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.binary (if subtract then .isub else .iadd) ty x y))
    {st next : State} {out : V} {trace : List RuleId} (selected : LowerSelection ctx i st out next trace) :
    selected.rule.id ∈ (if subtract then [747,748,599,746,749,745] else [595,597,596,598,590,589,592,591,594,593,588]) := by
  obtain ⟨_,data,_⟩ := stock_addsub_source_data inv subtract source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  cases subtract
  · simpa only [Bool.false_eq_true,ite_false,add_inventory] using member
  · simpa only [ite_true,sub_inventory] using member
end Backend.Stock.Proof.ScalarAddSub
