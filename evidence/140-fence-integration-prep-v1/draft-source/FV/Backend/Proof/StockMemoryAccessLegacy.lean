import FV.Backend.Proof.StockMemoryAccessTrap
import FV.Backend.Proof.LowerSimMemTrap

/-! Draft: this bridge remains pending the coherent legacy IselMemTrap provider.
The ordinary-access core does not import this file. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem accessAt_of_loop {sb : Nat} {inst : MInst} {value : CV} {uses : List CV}
    {world : Arm.ArmState} {code : Clif.TrapCode} {bytes : Nat}
    (shape : loopTrap? inst = some (code,bytes)) :
    AccessAt sb inst (value :: uses) world code (lo64 value) bytes := by
  cases inst <;> simp only [loopTrap?] at shape <;> try cases shape
  all_goals
    split at shape
    · rename_i atomic
      rename_i ty flags
      cases flag : flags.trapCode with
      | none => simp only [flag,Option.map_none] at shape; cases shape
      | some actual =>
        simp only [flag,Option.map_some,Option.some.injEq,Prod.mk.injEq] at shape
        obtain ⟨rfl,rfl⟩ := shape
        first | exact .rmw atomic flag | exact .cas atomic flag
    · cases shape

/-- The new boundary retains every original atomic-boundary theorem. -/
theorem VAccessTrapFrom.of_loop {sb : Nat} {vc : VCode} {sem : Backend.Proof.Sem}
    {initial : VState CV Arm.ArmState} {code : Clif.TrapCode}
    {addressProperty : BitVec 64 → Nat → Prop}
    (old : VMemTrapFrom vc sem initial code addressProperty) :
    VAccessTrapFrom sb vc sem initial code addressProperty := by
  obtain ⟨b,k,ρ,world,block,inst,operands,value,uses,bytes,path,foundBlock,foundInst,
    decoded,inputs,shape,property⟩ := old
  exact ⟨b,k,ρ,world,block,inst,operands,value :: uses,lo64 value,bytes,
    path,foundBlock,foundInst,decoded,inputs,accessAt_of_loop shape,property⟩

/-- The address property keeps the exact previous meaning. -/
theorem sourceAddrPred_eq_addrPred (Q : Nat → Nat → Prop) : sourceAddrPred Q = addrPred Q := rfl

end Backend.Stock.Proof.MemoryFaults
