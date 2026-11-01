import FV.Backend.Proof.StockMemorySretCopyFunctionObservation

namespace Backend.Stock.Memory.SretCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- Original source conditions for the three-block copy. Implicit sret returns remain permitted. -/
structure CfgClass (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  registers : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin
  shape : ∃ (entry middle target : Clif.Block)
      (i0 i8 j0 j8 base destination low high : Nat) (lf0 lf8 sf0 sf8 : Clif.MemFlags),
    f.blocks = [entry,middle,target] ∧
      entry.term = .jump ⟨middle.id,[]⟩ ∧ middle.term = .jump ⟨target.id,[]⟩ ∧ target.term = .ret [] ∧
      entry.id ≠ middle.id ∧ entry.id ≠ target.id ∧ middle.id ≠ target.id ∧
      (∀ stm ∈ entry.body,stm.inst = .nop) ∧ (∀ stm ∈ target.body,stm.inst = .nop) ∧
      middle.body[i0]? = some ⟨[low],.load .load .i64 lf0 base 0⟩ ∧
      middle.body[i8]? = some ⟨[high],.load .load .i64 lf8 base 8⟩ ∧
      middle.body[j0]? = some ⟨[],.store .store .i64 sf0 low destination 0⟩ ∧
      middle.body[j8]? = some ⟨[],.store .store .i64 sf8 high destination 8⟩ ∧
      i0 < j0 ∧ i8 < j8 ∧
      (∀ j stm,middle.body[j]? = some stm → j = i0 ∨ j = i8 ∨ j = j0 ∨ j = j8 ∨ stm.inst = .nop) ∧
      base ∈ entry.params.map (·.1) ∧ destination ∈ entry.params.map (·.1) ∧
      lf0.trapCode = none ∧ lf8.trapCode = none ∧ sf0.trapCode = none ∧ sf8.trapCode = none

end Backend.Stock.Memory.SretCopy
