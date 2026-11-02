import FV.Backend.Proof.StockMemoryAccessRegisterLevel

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An internal finite check of actual lowered memory forms. -/
def ordinaryAccessShapeB (inst : MInst) : Bool :=
  match inst with
  | .load op d am _ =>
    match op,d,am with
    | .uload64,.vreg _ .int,.unsignedOffset (.vreg _ .int) off => decide (off = 0 ∨ off = 16)
    | _,_,_ => false
  | .store op v am _ =>
    match op,v,am with
    | .store64,.vreg _ .int,.unsignedOffset (.vreg _ .int) off => decide (off = 8)
    | _,_,_ => false
  | .atomicRmwLoop .. | .atomicCasLoop .. => false
  | _ => true

/-- The internal check derives the access shape without a source acceptance guard. -/
theorem ordinaryAccessShape_of_check {sb : Nat} {inst : MInst} {uses : List CV}
    {world : Arm.ArmState} {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat}
    (checked : ordinaryAccessShapeB inst = true)
    (access : AccessAt sb inst uses world code address bytes) : OrdinaryAccessShape inst := by
  cases access with
  | load flag addr =>
    simp only [ordinaryAccessShapeB] at checked
    split at checked
    · rename_i d pointer off
      exact Or.inl ⟨d,pointer,off,_,of_decide_eq_true checked,rfl⟩
    · contradiction
  | store flag addr =>
    simp only [ordinaryAccessShapeB] at checked
    split at checked
    · rename_i stored pointer off
      have same : off = 8 := of_decide_eq_true checked
      subst off
      exact Or.inr ⟨stored,pointer,_,rfl⟩
    · contradiction
  | rmw atomic flag => simp [ordinaryAccessShapeB] at checked
  | cas atomic flag => simp [ordinaryAccessShapeB] at checked

/-- Every access of a checked virtual function has its internally derived shape. -/
theorem ordinaryAccessShapes_of_check {vc : VCode}
    (checked : vc.blocks.all (fun block => block.insts.all ordinaryAccessShapeB) = true)
    (b : Nat) (block : VBlock) (j : Nat) (inst : MInst)
    (found : vc.blocks[b]? = some block) (located : block.insts[j]? = some inst)
    {sb : Nat} {uses : List CV} {world : Arm.ArmState} {code : Clif.TrapCode}
    {address : BitVec 64} {bytes : Nat}
    (access : AccessAt sb inst uses world code address bytes) : OrdinaryAccessShape inst := by
  have row := (Array.all_eq_true_iff_forall_mem.mp checked) block (Array.mem_of_getElem? found)
  exact ordinaryAccessShape_of_check ((Array.all_eq_true_iff_forall_mem.mp row) inst
    (Array.mem_of_getElem? located)) access

end Backend.Stock.Proof.MemoryFaults
