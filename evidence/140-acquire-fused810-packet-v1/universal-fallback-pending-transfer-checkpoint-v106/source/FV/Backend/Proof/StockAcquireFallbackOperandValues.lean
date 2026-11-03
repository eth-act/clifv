import FV.Backend.Proof.StockAcquireFallbackPendingOperand

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- A successful current source extension needs only its actual operand binding.
Other pending results remain suspended and retain their original binding obligations. -/
theorem fallback_extend_selected_operand_values {f : Clif.Function} {ctx : Ctx} (inv : MappedCtxInv f ctx)
    (signed : Bool) {i x : Nat} {info : IInfo} {target : Clif.Ty}
    (installed : ctx.insts[i]? = some info)
    (source : info.clif = some (.extend (ScalarCast.extendOp signed) target x))
    {st next : State} {out : V} {rules : List RuleId}
    (selected : LowerSelection ctx i st out next rules) (chosen : selected.rule = ScalarCast.extendRule signed)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {frame : Clif.Frame} (dfg : DFGCons ctx frame) {value : Clif.Val} (lookup : frame.regs x = some value)
    (grows : value.ty.width < target.width)
    {aliases : Array (Option Nat)} {regs : Nat → CV} (bounded : aliases.size ≤ st.base.nextVreg)
    (held : ValueHeld ctx frame (fun key => regs (aliasNum aliases key)) x) :
    ∃ (sourceType : CTy) (pointer : Nat) (nextRegs : Nat → CV),ctx.valueType? x = some sourceType ∧
      ctx.valueReg? x = some (.vreg pointer .int) ∧
      out = .regsVec [[.vreg st.base.nextVreg .int]] ∧
      next = {st.mark x with base := (st.base.fresh .int).2.emit (.extend (.vreg st.base.nextVreg .int) (.vreg pointer .int) signed sourceType.bits target.width)} ∧
      PRun F isem [(MInst.extend (.vreg st.base.nextVreg .int) (.vreg pointer .int) signed sourceType.bits target.width).mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1))] regs nextRegs ∧
      VHolds ⟨target,ScalarCast.extendBits signed target.width value.bits⟩ (nextRegs st.base.nextVreg) ∧
      (∀ key,key ≠ st.base.nextVreg → nextRegs key = regs key) := by
  obtain ⟨sourceType,pointer,typed,accepted,mapped,output,nextEq⟩ :=
    fallback_extend_selected_shape inv signed installed source selected chosen
  have typeEq := (dfg.2 x sourceType value typed lookup).symm
  have fromEq : value.ty.width = sourceType.bits := by rw [typeEq,ofClif_bits]
  have fromWidths : sourceType.bits = 8 ∨ sourceType.bits = 16 ∨ sourceType.bits = 32 ∨ sourceType.bits = 64 := by
    simp only [eCTys,List.mem_cons,List.not_mem_nil,or_false] at accepted
    rcases accepted with rfl | rfl | rfl | rfl <;> decide
  have small := (fallback_extend_source_data inv signed installed source).1
  have sourceWidth : value.ty.width = 8 ∨ value.ty.width = 16 ∨ value.ty.width = 32 := by
    rcases fromWidths with h | h | h | h <;> omega
  have originalAccepted := inv.instE i info _ installed source
  have permitted : eTy target = true := by
    simpa [ScalarCast.extendOp,Compile.instE,Compile.tyE,eTy] using originalAccepted
  have widths : target.width = 8 ∨ target.width = 16 ∨ target.width = 32 ∨ target.width = 64 := by
    cases target <;> simp [eTy,Clif.Ty.width] at permitted ⊢
  have targetWidth : target.width = 16 ∨ target.width = 32 ∨ target.width = 64 := by
    rcases sourceWidth with h | h | h <;> rcases widths with h' | h' | h' | h' <;> omega
  have singleton : ValuesHeld (fun z => z = x) ctx frame (fun key => regs (aliasNum aliases key)) := by
    intro z equal
    subst z
    exact held
  obtain ⟨nextRegs,execution,valueHeld,kept⟩ := ScalarCast.stock_cast_extend_resolved refines signed sourceWidth
    targetWidth grows bounded mapped singleton (bits := value.bits)
    (by cases value; simp [Clif.Frame.getAs,Clif.Frame.get,lookup,Clif.Val.as?])
  refine ⟨sourceType,pointer,nextRegs,typed,mapped,output,nextEq,?_,valueHeld,kept⟩
  rw [← fromEq]
  exact execution

end Backend.Stock.Proof.Acquire810
