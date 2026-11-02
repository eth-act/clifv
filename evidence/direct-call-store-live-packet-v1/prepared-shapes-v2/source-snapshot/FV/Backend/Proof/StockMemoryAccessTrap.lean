import FV.Backend.Proof.LowerSeq

/-! Draft: no kernel command ran for this module.
This additive access boundary preserves the existing atomic-only interfaces. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The actual address, size and flag code at a lowered memory instruction.
Store addressing excludes the stored-value operand. -/
inductive AccessAt (sb : Nat) : MInst → List CV → Arm.ArmState →
    Clif.TrapCode → BitVec 64 → Nat → Prop where
  | load {op : LoadOp} {d : Reg} {am : AMode} {fl : Clif.MemFlags}
      {uses : List CV} {world : Arm.ArmState} {code : Clif.TrapCode} {address : BitVec 64}
      (flag : fl.trapCode = some code)
      (addr : amodeAddr sb am op.bytes uses world = some address) :
      AccessAt sb (.load op d am fl) uses world code address op.bytes
  | store {op : StoreOp} {valueReg : Reg} {am : AMode} {fl : Clif.MemFlags}
      {value : CV} {uses : List CV} {world : Arm.ArmState}
      {code : Clif.TrapCode} {address : BitVec 64}
      (flag : fl.trapCode = some code)
      (addr : amodeAddr sb am op.bytes uses world = some address) :
      AccessAt sb (.store op valueReg am fl) (value :: uses) world code address op.bytes
  | rmw {ty : CTy} {op : AtomicRmwLoopOp} {flags : Clif.MemFlags}
      {ra ro rd r1 r2 : Reg} {value : CV} {uses : List CV} {world : Arm.ArmState}
      {code : Clif.TrapCode} (atomic : AtomTy ty) (flag : flags.trapCode = some code) :
      AccessAt sb (.atomicRmwLoop ty op flags ra ro rd r1 r2) (value :: uses) world code (lo64 value) ty.bytes
  | cas {ty : CTy} {flags : Clif.MemFlags} {ra re rx rd r1 : Reg}
      {value : CV} {uses : List CV} {world : Arm.ArmState} {code : Clif.TrapCode}
      (atomic : AtomTy ty) (flag : flags.trapCode = some code) :
      AccessAt sb (.atomicCasLoop ty flags ra re rx rd r1) (value :: uses) world code (lo64 value) ty.bytes

/-- The source address property used by the existing memory-fault pipeline. -/
def sourceAddrPred (Q : Nat → Nat → Prop) : BitVec 64 → Nat → Prop :=
  fun address bytes => ∃ a,address = BitVec.ofNat 64 a ∧ Q a bytes

/-- Reach the real offending operation without executing its faulting access. -/
def VAccessTrapFrom (sb : Nat) (vc : VCode) (sem : Backend.Proof.Sem)
    (initial : VState CV Arm.ArmState) (code : Clif.TrapCode)
    (addressProperty : BitVec 64 → Nat → Prop) : Prop :=
  ∃ b k ρ world block inst operands uses address bytes,
    Star (VStep vc sem) (.run initial) (.run ⟨b,k,ρ,world⟩) ∧
    vc.blocks[b]? = some block ∧ block.insts[k]? = some inst ∧
    inst.operands = .ok operands ∧ vuses operands ρ = uses ∧
    AccessAt sb inst uses world code address bytes ∧ addressProperty address bytes

theorem VAccessTrapFrom.prefix {sb : Nat} {vc : VCode} {sem : Backend.Proof.Sem}
    {initial next : VState CV Arm.ArmState} {code : Clif.TrapCode}
    {addressProperty : BitVec 64 → Nat → Prop}
    (front : Star (VStep vc sem) (.run initial) (.run next))
    (fault : VAccessTrapFrom sb vc sem next code addressProperty) :
    VAccessTrapFrom sb vc sem initial code addressProperty := by
  obtain ⟨b,k,ρ,world,block,inst,operands,uses,address,bytes,path,rest⟩ := fault
  exact ⟨b,k,ρ,world,block,inst,operands,uses,address,bytes,front.trans path,rest⟩

end Backend.Stock.Proof.MemoryFaults
