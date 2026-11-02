import FV.Backend.Proof.StockMemoryAccessAllocated
import FV.Backend.Proof.StockMemoryAccessFaultSite

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- Internal instruction-shape obligation for the two loads and the computed store.
This predicate is not a compiler acceptance condition. -/
def OrdinaryAccessShape (inst : MInst) : Prop :=
  (∃ d pointer offset flags,(offset = 0 ∨ offset = 16) ∧
    inst = .load .uload64 (.vreg d .int) (.unsignedOffset (.vreg pointer .int) offset) flags) ∨
  (∃ stored pointer flags,inst = .store .store64 (.vreg stored .int)
    (.unsignedOffset (.vreg pointer .int) 8) flags)

/-- The original checker and realizer transfer an ordinary access to the actual machine fault site. -/
theorem access_register_level_boundary {R : RL} (wellFormed : R.Wf)
    {isem : Backend.Proof.Sem} {sb : Nat} {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (checked : CheckedAt R.vc R.rf cc ins a0)
    (realizes : Realizes R.vc R.rf isem ckeep R.step (QA R) R.GoodX)
    (initialValues : Loc → CV) (initialRegs : Nat → CV) (world : Arm.ArmState)
    (bindings : Inv ckeep a0 initialValues initialRegs (fun r => initialValues (.reg r)))
    {initial : Arm.ArmState} (entry : QA R initial (MConf.init R.rf initialValues world))
    (fault : VAccessTrapFrom sb R.vc isem ⟨0,0,initialRegs,world⟩ code property)
    (shapes : ∀ b block k inst,R.vc.blocks[b]? = some block → block.insts[k]? = some inst →
      ∀ uses world address bytes,AccessAt sb inst uses world code address bytes → OrdinaryAccessShape inst)
    (mp : ArmFault.MemMap)
    (unmapped : ∀ address bytes,property address bytes → ∃ k < bytes,mp (address+BitVec.ofNat 64 k) = .none) :
    ∃ n,TrapAtF mp R.fb R.base code (iterN R.step n initial) ∧
      ∀ j < n,R.GoodX (iterN R.step j initial) := by
  obtain ⟨n,b,k,allocs,items,values,next,block,inst,operands,address,bytes,
    related,found,located,valid,access,property,good⟩ :=
    access_allocated_boundary checked realizes initialValues initialRegs world bindings entry fault
  have missing := unmapped address bytes property
  rcases shapes b block k inst found located _ _ _ _ access with load | store
  · obtain ⟨d,pointer,offset,flags,sourceOffset,rfl⟩ := load
    exact ⟨n,load_unsigned_fault_site wellFormed related found located sourceOffset valid access missing,good⟩
  · obtain ⟨stored,pointer,flags,rfl⟩ := store
    exact ⟨n,store_eight_fault_site wellFormed related found located valid access missing,good⟩

end Backend.Stock.Proof.MemoryFaults
