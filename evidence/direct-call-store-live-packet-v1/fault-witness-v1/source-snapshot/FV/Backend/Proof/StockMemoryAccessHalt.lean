import FV.Backend.Proof.StockMemoryAccessTrap

/-! Additive proof semantics for the first actual access boundary.
This module changes no compiler or machine semantics. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

def HaltsAtAccess (sb : Nat) (code : Clif.TrapCode) (property : BitVec 64 → Nat → Prop)
    (inst : MInst) (uses : List CV) (world : Arm.ArmState) : Prop :=
  ∃ address bytes,AccessAt sb inst uses world code address bytes ∧ property address bytes

private def haltOutputs (inst : MInst) : List CV :=
  match inst.operands with
  | .ok operands => (operands.toList.filter Operand.isDef).map (fun _ => 0)
  | .error _ => []

open Classical in
noncomputable def haltAccess (sb : Nat) (code : Clif.TrapCode)
    (property : BitVec 64 → Nat → Prop) (isem : Backend.Proof.Sem) : Backend.Proof.Sem :=
  fun inst uses world => if HaltsAtAccess sb code property inst uses world then
    some (haltOutputs inst,world,.halt) else isem inst uses world

private theorem haltAccess_of_not {sb : Nat} {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop} {isem : Backend.Proof.Sem} {inst : MInst}
    {uses : List CV} {world : Arm.ArmState}
    (normal : ¬ HaltsAtAccess sb code property inst uses world) :
    haltAccess sb code property isem inst uses world = isem inst uses world := by
  simp [haltAccess,normal]

private theorem haltAccess_of {sb : Nat} {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop} {isem : Backend.Proof.Sem} {inst : MInst}
    {uses : List CV} {world : Arm.ArmState}
    (fault : HaltsAtAccess sb code property inst uses world) :
    haltAccess sb code property isem inst uses world = some (haltOutputs inst,world,.halt) := by
  simp [haltAccess,fault]

private theorem haltOutputs_length {inst : MInst} {operands : Array Operand}
    (valid : inst.operands = .ok operands) :
    (haltOutputs inst).length = (operands.toList.filter Operand.isDef).length := by
  simp [haltOutputs,valid]

/-- A real prefix reaches its first matching access under the additive proof semantics. -/
theorem star_haltAccess {sb : Nat} {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop} {vc : VCode} {isem : Backend.Proof.Sem} :
    ∀ {before after : VConf CV Arm.ArmState},Star (VStep vc isem) before after →
      ∀ {last : VState CV Arm.ArmState},after = .run last →
      (∃ block inst operands,vc.blocks[last.b]? = some block ∧ block.insts[last.k]? = some inst ∧
        inst.operands = .ok operands ∧ HaltsAtAccess sb code property inst (vuses operands last.ρ) last.w) →
      ∃ reached : VState CV Arm.ArmState,
        Star (VStep vc (haltAccess sb code property isem)) before (.run reached) ∧
        ∃ block inst operands,vc.blocks[reached.b]? = some block ∧ block.insts[reached.k]? = some inst ∧
          inst.operands = .ok operands ∧
          HaltsAtAccess sb code property inst (vuses operands reached.ρ) reached.w := by
  intro before after path
  induction path with
  | refl => intro last same boundary; subst same; exact ⟨last,.refl _,boundary⟩
  | step head tail ih =>
    intro last same boundary
    cases head with
    | @step b k regs world block inst operands outs next ctl result found located valid execution length advance =>
      by_cases fault : HaltsAtAccess sb code property inst (vuses operands regs) world
      · exact ⟨⟨b,k,regs,world⟩,.refl _,block,inst,operands,found,located,valid,fault⟩
      · obtain ⟨reached,path',boundary'⟩ := ih same boundary
        have execution' : haltAccess sb code property isem inst
            ((operands.toList.filter Operand.isUse).map (regs ·.vreg)) world = some (outs,next,ctl) := by
          change haltAccess sb code property isem inst (vuses operands regs) world = _
          rw [haltAccess_of_not fault]
          exact execution
        exact ⟨reached,.step (VStep.step found located valid execution' length advance) path',boundary'⟩

/-- The actual access outcome becomes a real halt at its first matching instruction. -/
theorem accessTrap_halt {sb : Nat} {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop} {vc : VCode} {isem : Backend.Proof.Sem}
    {initial : VState CV Arm.ArmState}
    (fault : VAccessTrapFrom sb vc isem initial code property) :
    ∃ reached : VState CV Arm.ArmState,
      Star (VStep vc (haltAccess sb code property isem)) (.run initial) (.run reached) ∧
      ∃ block inst operands,vc.blocks[reached.b]? = some block ∧ block.insts[reached.k]? = some inst ∧
        inst.operands = .ok operands ∧
        HaltsAtAccess sb code property inst (vuses operands reached.ρ) reached.w ∧
        VStep vc (haltAccess sb code property isem) (.run reached) (.halt reached.w) := by
  obtain ⟨b,k,regs,world,block,inst,operands,uses,address,bytes,path,found,located,valid,values,access,holds⟩ := fault
  have matching : HaltsAtAccess sb code property inst (vuses operands regs) world := by
    rw [values]
    exact ⟨address,bytes,access,holds⟩
  obtain ⟨reached,path',block',inst',operands',found',at',valid',matching'⟩ :=
    star_haltAccess path rfl ⟨block,inst,operands,found,located,valid,matching⟩
  exact ⟨reached,path',block',inst',operands',found',at',valid',matching',
    VStep.step found' at' valid' (haltAccess_of matching') (haltOutputs_length valid') VNext.halt⟩

end Backend.Stock.Proof.MemoryFaults
