import FV.Backend.Proof.StockMemoryAccessTrap

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Invert an actual lowered load boundary without an additional shape certificate. -/
theorem AccessAt.load_inv {sb : Nat} {op : LoadOp} {d : Reg} {am : AMode} {flags : Clif.MemFlags}
    {uses : List CV} {world : Arm.ArmState} {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat}
    (access : AccessAt sb (.load op d am flags) uses world code address bytes) :
    bytes = op.bytes ∧ flags.trapCode = some code ∧
      amodeAddr sb am op.bytes uses world = some address := by
  cases access with
  | load flag address => exact ⟨rfl,flag,address⟩

/-- Invert an actual lowered store boundary and exclude its value from address uses. -/
theorem AccessAt.store_inv {sb : Nat} {op : StoreOp} {v : Reg} {am : AMode} {flags : Clif.MemFlags}
    {uses : List CV} {world : Arm.ArmState} {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat}
    (access : AccessAt sb (.store op v am flags) uses world code address bytes) :
    ∃ value addressUses,uses = value :: addressUses ∧ bytes = op.bytes ∧ flags.trapCode = some code ∧
      amodeAddr sb am op.bytes addressUses world = some address := by
  cases access with
  | store flag address => exact ⟨_,_,rfl,rfl,flag,address⟩

end Backend.Stock.Proof.MemoryFaults
