import FV.Backend.Proof.StockAcquireTwoLoadOriginalSource

namespace Backend.Stock.Proof.AcquireTwoLoadPrefix
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

private theorem frame_equal {a b : Clif.Frame} (function : a.func = b.func) (registers : a.regs = b.regs)
    (slots : a.slots = b.slots) (body : a.body = b.body) (term : a.term = b.term) : a = b := by
  cases a
  cases b
  simp_all

/-- Original public source entry derives both pointers and the exact source frame; no caller supplies a normal form. -/
theorem original_entry_normal_form {args : List Clif.Val} {state : Clif.State}
    (entered : ClifEntry function args state) :
    ∃ (firstPointer secondPointer : BitVec 64),args = [⟨.i64,firstPointer⟩,⟨.i64,secondPointer⟩] ∧
      state.frame = entry firstPointer secondPointer ∧ state.callers = [] := by
  have signature := entered.sig
  cases args with
  | nil => simp [function] at signature
  | cons first rest =>
    cases rest with
    | nil => simp [function] at signature
    | cons second rest =>
      cases rest with
      | cons other tail => simp [function] at signature
      | nil =>
        obtain ⟨firstType,firstBits⟩ := first
        obtain ⟨secondType,secondBits⟩ := second
        have types : firstType = .i64 ∧ secondType = .i64 := by simpa [function] using signature
        rcases types with ⟨rfl,rfl⟩
        obtain ⟨block,present,body,term,paramTypes,registers⟩ := entered.entry
        have sameBlock : block = function.blocks[0]! := by simpa [Clif.Function.entry?,function] using present.symm
        subst block
        obtain ⟨canonicalBlock,canonicalRegs,canonicalAt,canonicalTypes,canonicalParams,canonicalSet,canonicalFrame⟩ := source_entry_pointers firstBits secondBits
        have canonicalBlockEq : canonicalBlock = function.blocks[0]! := by
          simpa [Clif.Function.entry?,function] using canonicalAt.symm
        subst canonicalBlock
        have canonicalRegsEq : (entry firstBits secondBits).regs = canonicalRegs := congrArg Clif.Frame.regs canonicalFrame
        rw [← canonicalRegsEq] at canonicalSet
        have sameRegisters : (entry firstBits secondBits).regs = state.frame.regs := Option.some.inj (canonicalSet.symm.trans registers)
        have sameSlots : state.frame.slots = [] := by simpa [function] using entered.slotIds
        refine ⟨firstBits,secondBits,rfl,?_,entered.callers⟩
        exact frame_equal entered.func sameRegisters.symm sameSlots body term

end Backend.Stock.Proof.AcquireTwoLoadPrefix
