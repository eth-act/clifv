import FV.Backend.Proof.StockAcquireTrapBoundary

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The exact acquire operand and its original memory trap code. -/
inductive AcquireAt : MInst → List CV → Arm.ArmState →
    Clif.TrapCode → BitVec 64 → Nat → Prop where
  | acquire {ty : CTy} {d pointer : Reg} {flags : Clif.MemFlags}
      {value : CV} {world : Arm.ArmState} {code : Clif.TrapCode}
      (atomic : AtomTy ty) (flag : flags.trapCode = some code) :
      AcquireAt (.loadAcquire ty d pointer flags) [value] world code (lo64 value) ty.bytes

def VAcquireBoundaryFrom (vc : VCode) (sem : Backend.Proof.Sem)
    (initial : VState CV Arm.ArmState) (code : Clif.TrapCode)
    (property : BitVec 64 → Nat → Prop) : Prop :=
  ∃ b k regs world block inst operands uses address bytes,
    Star (VStep vc sem) (.run initial) (.run ⟨b,k,regs,world⟩) ∧
    vc.blocks[b]? = some block ∧ block.insts[k]? = some inst ∧
    inst.operands = .ok operands ∧ vuses operands regs = uses ∧
    AcquireAt inst uses world code address bytes ∧ property address bytes

/-- The original reached acquire supplies the exact operand boundary internally. -/
theorem VAcquireTrapFrom.boundary {vc : VCode} {isem : Backend.Proof.Sem}
    {initial : VState CV Arm.ArmState} {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (fault : VAcquireTrapFrom vc isem initial code property) :
    VAcquireBoundaryFrom vc isem initial code property := by
  obtain ⟨b,k,regs,world,block,ty,d,pointer,flags,path,found,located,atomic,flag,holds⟩ := fault
  exact ⟨b,k,regs,world,block,_,_,[regs pointer],lo64 (regs pointer),ty.bytes,
    path,found,located,rfl,rfl,.acquire atomic flag,holds⟩

def HaltsAtAcquire (code : Clif.TrapCode) (property : BitVec 64 → Nat → Prop)
    (inst : MInst) (uses : List CV) (world : Arm.ArmState) : Prop :=
  ∃ address bytes,AcquireAt inst uses world code address bytes ∧ property address bytes

private def haltOutputs (inst : MInst) : List CV :=
  match inst.operands with
  | .ok operands => (operands.toList.filter Operand.isDef).map (fun _ => 0)
  | .error _ => []

open Classical in
noncomputable def haltAcquire (code : Clif.TrapCode)
    (property : BitVec 64 → Nat → Prop) (isem : Backend.Proof.Sem) : Backend.Proof.Sem :=
  fun inst uses world => if HaltsAtAcquire sb code property inst uses world then
    some (haltOutputs inst,world,.halt) else isem inst uses world

private theorem haltAcquire_of_not {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop} {isem : Backend.Proof.Sem} {inst : MInst}
    {uses : List CV} {world : Arm.ArmState}
    (normal : ¬ HaltsAtAcquire sb code property inst uses world) :
    haltAcquire sb code property isem inst uses world = isem inst uses world := by
  simp [haltAcquire,normal]

private theorem haltAcquire_of {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop} {isem : Backend.Proof.Sem} {inst : MInst}
    {uses : List CV} {world : Arm.ArmState}
    (fault : HaltsAtAcquire sb code property inst uses world) :
    haltAcquire sb code property isem inst uses world = some (haltOutputs inst,world,.halt) := by
  simp [haltAcquire,fault]

private theorem haltOutputs_length {inst : MInst} {operands : Array Operand}
    (valid : inst.operands = .ok operands) :
    (haltOutputs inst).length = (operands.toList.filter Operand.isDef).length := by
  simp [haltOutputs,valid]

/-- A real prefix reaches its first matching access under the additive proof semantics. -/
theorem star_haltAcquire {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop} {vc : VCode} {isem : Backend.Proof.Sem} :
    ∀ {before after : VConf CV Arm.ArmState},Star (VStep vc isem) before after →
      ∀ {last : VState CV Arm.ArmState},after = .run last →
      (∃ block inst operands,vc.blocks[last.b]? = some block ∧ block.insts[last.k]? = some inst ∧
        inst.operands = .ok operands ∧ HaltsAtAcquire sb code property inst (vuses operands last.ρ) last.w) →
      ∃ reached : VState CV Arm.ArmState,
        Star (VStep vc (haltAcquire sb code property isem)) before (.run reached) ∧
        ∃ block inst operands,vc.blocks[reached.b]? = some block ∧ block.insts[reached.k]? = some inst ∧
          inst.operands = .ok operands ∧
          HaltsAtAcquire sb code property inst (vuses operands reached.ρ) reached.w := by
  intro before after path
  induction path with
  | refl => intro last same boundary; subst same; exact ⟨last,.refl _,boundary⟩
  | step head tail ih =>
    intro last same boundary
    cases head with
    | @step b k regs world block inst operands outs next ctl result found located valid execution length advance =>
      by_cases fault : HaltsAtAcquire sb code property inst (vuses operands regs) world
      · exact ⟨⟨b,k,regs,world⟩,.refl _,block,inst,operands,found,located,valid,fault⟩
      · obtain ⟨reached,path',boundary'⟩ := ih same boundary
        have execution' : haltAcquire sb code property isem inst
            ((operands.toList.filter Operand.isUse).map (regs ·.vreg)) world = some (outs,next,ctl) := by
          change haltAcquire sb code property isem inst (vuses operands regs) world = _
          rw [haltAcquire_of_not fault]
          exact execution
        exact ⟨reached,.step (VStep.step found located valid execution' length advance) path',boundary'⟩

/-- The actual access outcome becomes a real halt at its first matching instruction. -/
theorem acquireTrap_halt {code : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop} {vc : VCode} {isem : Backend.Proof.Sem}
    {initial : VState CV Arm.ArmState}
    (fault : VAcquireBoundaryFrom vc isem initial code property) :
    ∃ reached : VState CV Arm.ArmState,
      Star (VStep vc (haltAcquire sb code property isem)) (.run initial) (.run reached) ∧
      ∃ block inst operands,vc.blocks[reached.b]? = some block ∧ block.insts[reached.k]? = some inst ∧
        inst.operands = .ok operands ∧
        HaltsAtAcquire sb code property inst (vuses operands reached.ρ) reached.w ∧
        VStep vc (haltAcquire sb code property isem) (.run reached) (.halt reached.w) := by
  obtain ⟨b,k,regs,world,block,inst,operands,uses,address,bytes,path,found,located,valid,values,access,holds⟩ := fault
  have matching : HaltsAtAcquire sb code property inst (vuses operands regs) world := by
    rw [values]
    exact ⟨address,bytes,access,holds⟩
  obtain ⟨reached,path',block',inst',operands',found',at',valid',matching'⟩ :=
    star_haltAcquire path rfl ⟨block,inst,operands,found,located,valid,matching⟩
  exact ⟨reached,path',block',inst',operands',found',at',valid',matching',
    VStep.step found' at' valid' (haltAcquire_of matching') (haltOutputs_length valid') VNext.halt⟩

end Backend.Stock.Proof.Acquire810
