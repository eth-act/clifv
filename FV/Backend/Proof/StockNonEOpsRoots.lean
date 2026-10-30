import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.IselExclData
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program

/-- The closure roots whose primary source opcode is outside `eOps`: scalar-float constants,
arithmetic, rounding, conversions and comparison, the bitcasts, and the `trap`/`return`
terminator roots. -/
def nonEOpsRootIds : List RuleId :=
  [584,585,662,664,666,668,670,672,674,676,678,679,680,682,683,685,686,688,689,691,692,
   723,724,725,726,729,730,731,732,735,736,737,738,741,742,743,744,951,
   1080,1083,1084,1085,964,1037]

/-- Checked syntactic inventory: no listed root has a primary source opcode in `eOps`. -/
theorem stock_nonEOps_root_opcodes :
    (program.rulesOf TId.lower).all (fun r => !nonEOpsRootIds.contains r.id ||
      match sourceRuleOpcode program r with
      | some k => !eOps.contains k
      | none => true) = true := by
  rw [show TId.lower = 686 from rfl,data_program.r686]
  decide +kernel

/-- An actually selected source-statement root belongs to the candidate list of an `eOps`
opcode, derived from the unchanged mapped context; no rule-id certificate is supplied. -/
theorem stock_selected_source_eOps {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) {before after : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i before out after trace) :
    ∃ ko ∈ eOps, selected.rule.id ∈ sourceOpcodeIds ko := by
  obtain ⟨kf,ko,fs,data,member⟩ :=
    instData_shape (mapped.instE i info inst source clif) (mapped.data i info inst source clif)
  exact ⟨ko,member,stock_selected_source_opcode_ids mapped source clif data selected⟩

/-- No actual source-statement selection picks a root whose primary opcode is outside `eOps`:
the scalar-float, float-conversion, float-comparison and bitcast roots are unmatchable for
Stock under the original mapped context. -/
theorem stock_selected_source_not_nonEOps {f : Clif.Function} {ctx : Ctx} (mapped : MappedCtxInv f ctx)
    {i : Nat} {info : IInfo} {inst : Clif.Inst} (source : ctx.insts[i]? = some info)
    (clif : info.clif = some inst) {before after : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i before out after trace) :
    selected.rule.id ∉ nonEOpsRootIds := by
  obtain ⟨ko,member,ids⟩ := stock_selected_source_eOps mapped source clif selected
  intro listed
  unfold sourceOpcodeIds at ids
  obtain ⟨r,filtered,same⟩ := List.mem_map.mp ids
  obtain ⟨rule,cond⟩ := List.mem_filter.mp filtered
  simp only [Bool.and_eq_true,beq_iff_eq] at cond
  have checked := List.all_eq_true.mp stock_nonEOps_root_opcodes r rule
  rw [same,cond.2] at checked
  simp only [List.contains_iff_mem.mpr listed,List.contains_iff_mem.mpr member,Bool.not_true,
    Bool.or_self,Bool.false_eq_true] at checked
end Backend.Stock.Proof
