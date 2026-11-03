import FV.Backend.Proof.StockAcquireFallbackExtendEncoded

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Successful final layout derives the exact encoder fields of every retained instruction line. -/
theorem layout_instruction_arm_fields {fa : FnAsm} {fb : FnBin} (layout : fa.layout = .ok fb)
    {j : Nat} {instruction : Insn} {trap : Option Clif.TrapCode}
    (found : fa.lines.toList[j]? = some (.ins instruction trap)) :
    ∃ (labels : Std.HashMap Lbl Nat) (fields : ArmInst),labelOffsets fa.lines = .ok labels ∧
      instruction.armFields ⟨lineOffset fa.lines.toList j,(labels[·]?)⟩ = .ok fields := by
  obtain ⟨labels,labelMap⟩ := FnAsm.layout_labelOffsets layout
  obtain ⟨aligned,word,decoded,located,encoded,same⟩ := FnAsm.layout_insn layout labelMap found
  unfold Insn.toArmInst at encoded
  cases actual : instruction.armFields ⟨lineOffset fa.lines.toList j,(labels[·]?)⟩ with
  | error message => simp only [actual,Functor.map,Except.map] at encoded;cases encoded
  | ok fields => exact ⟨labels,fields,labelMap,actual⟩

/-- Final encoding supplies both bitfield bounds, without a source instruction outcome or new guard. -/
theorem layout_bitfield_bounds {fa : FnAsm} {fb : FnBin} (layout : fa.layout = .ok fb)
    {j immr imms : Nat} {op : BfmOp} {wide : Bool} {dest pointer : Reg}
    {trap : Option Clif.TrapCode}
    (found : fa.lines.toList[j]? = some (.ins (.bfm op wide dest pointer immr imms) trap)) :
    immr < (if wide then 64 else 32) ∧ imms < (if wide then 64 else 32) := by
  obtain ⟨labels,fields,labelMap,encoded⟩ := layout_instruction_arm_fields layout found
  unfold Insn.armFields at encoded
  split at encoded
  · cases encoded
  · rename_i accepted
    simp only [Bool.or_eq_true,decide_eq_true_eq,not_or] at accepted
    constructor <;> omega

end Backend.Stock.Proof.Acquire810
