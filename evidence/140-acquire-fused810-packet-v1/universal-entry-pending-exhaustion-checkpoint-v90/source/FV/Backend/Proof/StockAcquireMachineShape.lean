import FV.Backend.Proof.StockAcquireMachineCheckW

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Original form coverage derives the virtual acquire operands needed by the allocator transfer. -/
theorem acquire_shape_of_forms_covered {vc : VCode} {ctx : FnCtx} (covered : FormsCovered ctx vc)
    {b j : Nat} {block : VBlock} {inst : MInst}
    (found : vc.blocks[b]? = some block) (located : block.insts[j]? = some inst)
    {uses : List CV} {world : Arm.ArmState} {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat}
    (access : AcquireAt inst uses world code address bytes) :
    ∃ ty dest pointer flags,inst = .loadAcquire ty (.vreg dest .int) (.vreg pointer .int) flags := by
  have form := covered b block j inst found located
  cases access with
  | @acquire ty dest pointer flags value world code atomic flag =>
    rcases form with control | form
    · simp [MInst.isCtl] at control
    · cases dest <;> cases pointer <;> (try cases ‹RegClass›) <;> (try cases ‹RegClass›) <;> simp_all [FormOk]
      all_goals exact ⟨ty,_,_,flags,rfl⟩

end Backend.Stock.Proof.Acquire810
