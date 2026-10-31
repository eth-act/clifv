import FV.Backend.Proof.StockMemoryExtLoadMatch
import FV.Backend.Proof.StockRootOpcodeMatch
import FV.Backend.Proof.IselCtlRuleIds

namespace Backend.Stock.Memory.ExtendedRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem opcode_inventory (kind : Kind) :
    sourceOpcodeIds kind.sourceTag = [kind.root.id] := by
  cases kind <;> decide +kernel

section SourceData
attribute [local semireducible] Isle.Aarch64.program

/-- Original source metadata supplies the load opcode and little-endian condition.
The result type remains arbitrary; the source invariant supplies its validity. -/
theorem extending_load_source_data (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.load kind.sourceOp ty flags x 0)) :
    flags.endianness ≠ some .big ∧
      info.data = .data 152 16
        [.data 151 kind.sourceTag [],.value x,.op (.memFlags flags),.int 0] := by
  have data := inv.data i info _ source clif
  change (if (!eTy ty && !(ty.isFloat && kind.sourceOp == .load)) = true then
      Except.error s!"load.{ty.name}"
    else if (flags.endianness == some .big) = true then Except.error "big-endian load"
    else Except.ok (instDataV "Load"
      [opcodeV (loadOpcode kind.sourceOp),.value x,.op (.memFlags flags),.int 0])) =
        Except.ok info.data at data
  by_cases invalid : (!eTy ty && !(ty.isFloat && kind.sourceOp == .load)) = true
  · rw [if_pos invalid] at data
    cases data
  · rw [if_neg invalid] at data
    have accepted : ¬ (flags.endianness == some .big) = true := by
      intro big
      rw [if_pos big] at data
      cases data
    have little : flags.endianness ≠ some .big := by
      intro big
      apply accepted
      simp [big]
    rw [if_neg accepted] at data
    refine ⟨little,(Except.ok.inj data).symm.trans ?_⟩
    cases kind <;> rfl

end SourceData

/-- The unique original source opcode determines the retained root internally.
No global exclusion of load instructions is required. -/
theorem stock_selected_extending_load_rule (kind : Kind) {ty : Clif.Ty}
    {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    {i x : Nat} {info : IInfo} {flags : Clif.MemFlags}
    (source : ctx.insts[i]? = some info)
    (clif : info.clif = some (.load kind.sourceOp ty flags x 0))
    {st next : State} {out : V} {trace : List RuleId}
    (selected : LowerSelection ctx i st out next trace) : selected.rule = kind.root := by
  obtain ⟨little,data⟩ := extending_load_source_data kind inv source clif
  have member := stock_selected_source_opcode_ids inv source clif data selected
  rw [opcode_inventory] at member
  have idEq : selected.rule.id = kind.root.id := List.mem_singleton.mp member
  have candidate : kind.root ∈ program.rulesOf T.lower.id := by
    cases kind <;> rw [show T.lower.id = 686 from rfl,data_program.r686]
    all_goals decide +kernel
  exact eq_of_mem_of_id lower_ids_nodup selected.rule_mem candidate idEq

end Backend.Stock.Memory.ExtendedRoots
