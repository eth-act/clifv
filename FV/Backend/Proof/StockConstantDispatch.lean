module

public import FV.Backend.Proof.StockConstantRecordValues
public import FV.Backend.Proof.StockRootOpcodeMatch

@[expose] public section

/-! Constant dispatch derived from original source data and actual first-match selection. -/
namespace Backend.Stock.Proof.ConstantComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem inventory : sourceOpcodeIds 57 = [rule_lower_53.id] := by
  unfold sourceOpcodeIds
  rw [show TId.lower = 686 from rfl, data_program.r686]
  decide +kernel

section Source
attribute [local semireducible] Isle.Aarch64.program
private theorem source_data {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.iconst ty imm)) :
    info.data = .data 152 35 [.data 151 57 [], .int (imm64OfIconst ty imm)] := by
  have supported := inv.instE i info _ source clif
  have he : eTy ty = true := by simpa [Compile.instE,Compile.tyE,eTy] using supported
  have data := inv.data i info _ source clif
  have shape : instData f (.iconst ty imm) =
      .ok (.data 152 35 [.data 151 57 [], .int (imm64OfIconst ty imm)]) := by
    simp only [instData,he,ite_true]; rfl
  exact Except.ok.inj (data.symm.trans shape)
end Source

/-- A successful original integer constant selects its unique production root;
no root ID, immediate restriction, or caller-supplied match certificate is needed. -/
theorem selected_rule {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width}
    (source : ctx.insts[i]? = some info) (clif : info.clif = some (.iconst ty imm))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = rule_lower_53 := by
  have member := stock_selected_source_opcode_ids inv source clif (source_data inv source clif) selected
  rw [inventory,List.mem_singleton] at member
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem
    (by change rule_lower_53 ∈ program.rulesOf 686; rw [data_program.r686]; decide +kernel) member

end Backend.Stock.Proof.ConstantComplete
