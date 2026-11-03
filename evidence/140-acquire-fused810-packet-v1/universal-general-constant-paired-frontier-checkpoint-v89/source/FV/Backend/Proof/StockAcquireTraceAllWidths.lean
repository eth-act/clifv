import FV.Backend.Proof.StockAcquireTrace
import FV.Backend.Proof.StockAcquireRegisterLevelAllWidths

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The checked allocator transfers the exact acquire for every original width to its linked fault site. -/
theorem acquire_all_widths_register_level_boundary_from_trace {R : RL} {good : Arm.ArmState → Prop} (wellFormed : R.Wf)
    {isem : Backend.Proof.Sem} {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (checked : CheckedAt R.vc R.rf cc ins a0)
    (realizes : Realizes R.vc R.rf isem ckeep R.step (QA R) good)
    (initialValues : Loc → CV) (initialRegs : Nat → CV) (world : Arm.ArmState)
    (bindings : Inv ckeep a0 initialValues initialRegs (fun r => initialValues (.reg r)))
    {initial : Arm.ArmState} (entry : QA R initial (MConf.init R.rf initialValues world))
    (fault : VAcquireBoundaryFrom R.vc isem ⟨0,0,initialRegs,world⟩ code property)
    (shapes : ∀ (b : Nat) (block : VBlock) (k : Nat) (inst : MInst),
      R.vc.blocks[b]? = some block → block.insts[k]? = some inst →
      ∀ (uses : List CV) (world : Arm.ArmState) (address : BitVec 64) (bytes : Nat),
        AcquireAt inst uses world code address bytes →
          ∃ ty d pointer flags,inst = .loadAcquire ty (.vreg d .int) (.vreg pointer .int) flags)
    (mp : ArmFault.MemMap)
    (unmapped : ∀ address bytes,property address bytes → ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) :
    ∃ n,TrapAtF mp R.fb R.base code (iterN R.step n initial) ∧
      ∀ j < n,good (iterN R.step j initial) := by
  obtain ⟨n,b,k,allocs,items,values,next,block,inst,operands,address,bytes,
    related,found,located,valid,access,property,good⟩ :=
    acquire_allocated_boundary_trace checked realizes initialValues initialRegs world bindings entry fault
  obtain ⟨ty,d,pointer,flags,rfl⟩ := shapes b block k inst found located _ _ _ _ access
  exact ⟨n,acquire_all_widths_fault_site wellFormed related found located valid access (unmapped _ _ property),good⟩

end Backend.Stock.Proof.Acquire810
