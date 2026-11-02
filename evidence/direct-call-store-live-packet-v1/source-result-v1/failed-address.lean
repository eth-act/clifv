import FV.Backend.Proof.StockMemoryLoad

namespace Backend.Stock.Proof.CallStoreResult
open Backend Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The preserved original i64 pointer computes the existing offset8 store address. -/
theorem pointer_address {sb register : Nat} {pointer : Clif.Val} {value : CV}
    (held : VHolds pointer value) (typed : pointer.ty = .i64) (world : Arm.ArmState) :
    amodeAddr sb (.unsignedOffset (.vreg register .int) 8) 8 [value] world =
      some (BitVec.ofNat 64 (Clif.effAddr pointer 8)) := by
  simp only [amodeAddr,ite_eq_left (show 8 % 8 = 0 ∧ 8 ≤ 4095*8 from by decide)]
  rw [lo64_of_holds held typed]
  rw [← BitVec.ofInt_natCast,← BitVec.ofInt_natCast,← BitVec.ofInt_add,effAddr_ofInt]

end Backend.Stock.Proof.CallStoreResult
