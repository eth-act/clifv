import FV.Backend.Proof.StockMemoryAccessTrap
import FV.Backend.Proof.PrepareSound
import FV.Backend.Proof.DeadCleanupPrepare

/-! Draft additive preparation transfer. The old memory-trap variants stay unchanged. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem access_not_pure {sb : Nat} {i : MInst} {uses : List CV} {world : Arm.ArmState}
    {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat}
    (access : AccessAt sb i uses world code address bytes) : DeadCleanup.pureForm i = false := by
  cases access <;> rfl

private theorem access_not_cmp {sb : Nat} {i : MInst} {uses : List CV} {world : Arm.ArmState}
    {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat}
    (access : AccessAt sb i uses world code address bytes) : DeadCleanup.cmpForm i = false := by
  cases access <;> rfl

private theorem access_not_jump {sb : Nat} {i : MInst} {uses : List CV} {world : Arm.ArmState}
    {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat}
    (access : AccessAt sb i uses world code address bytes) : DeadCleanup.isJump i = false := by
  cases access <;> rfl

private theorem access_not_retarget {sb : Nat} {i i' : MInst} {uses : List CV} {world : Arm.ArmState}
    {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat} {labels : List Label}
    (access : AccessAt sb i uses world code address bytes) (targets : i.setTargets labels = some i') : False := by
  cases access <;> simp [MInst.setTargets] at targets

private theorem entry_block {vc : VCode} {isem : Backend.Proof.Sem} {ρ : Nat → CV} {world : Arm.ArmState}
    {state : VState CV Arm.ArmState} {block : VBlock}
    (path : Star (VStep vc isem) (.run ⟨0,0,ρ,world⟩) (.run state))
    (found : vc.blocks[state.b]? = some block) : ∃ initial,vc.blocks[0]? = some initial := by
  cases path with
  | refl => exact ⟨block,found⟩
  | step head tail => cases head with | step initial _ _ _ _ _ => exact ⟨_,initial⟩

/-- Cleanup retains every real access boundary, with its original operand values and world. -/
theorem accessTraps_clean {sb : Nat} {vc : VCode} {isem : Backend.Proof.Sem}
    (pure : ∀ i uses world outs next ctl,DeadCleanup.pureForm i = true →
      isem i uses world = some (outs,next,ctl) → next = world ∧ ctl = .next)
    (compares : DeadCleanup.CmpOverwrite isem)
    (terminated : ∀ block ∈ vc.blocks.toList,∃ last,block.insts.back? = some last ∧ last.isTerminator = true)
    {ρ : Nat → CV} {world : Arm.ArmState} {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    (fault : VAccessTrapFrom sb vc isem ⟨0,0,ρ,world⟩ code property) :
    VAccessTrapFrom sb (DeadCleanup.clean vc) isem ⟨0,0,ρ,world⟩ code property := by
  obtain ⟨b,k,regs,next,block,inst,ops,uses,address,bytes,path,found,located,operands,values,access,holds⟩ := fault
  obtain ⟨initial,entry⟩ := entry_block path found
  obtain ⟨state,path',related⟩ := DeadCleanup.star_sim pure compares terminated
    (DeadCleanup.rel_entry entry ρ world) path
  obtain ⟨k',regs',rfl,found',at',keptUses⟩ := DeadCleanup.rel_kept related found located operands
    (access_not_pure access) (access_not_cmp access) (access_not_jump access)
  exact ⟨b,k',regs',next,DeadCleanup.cleanBlock vc 0 block,inst,ops,uses,address,bytes,
    path',found',at',operands,keptUses.symm.trans values,access,holds⟩

/-- CFG pruning retains the same access boundary under the original cleanup semantics. -/
theorem accessTraps_prune {sb : Nat} {vc : VCode} {isem : Backend.Proof.Sem}
    (pure : ∀ i uses world outs next ctl,DeadCleanup.pureForm i = true →
      isem i uses world = some (outs,next,ctl) → next = world ∧ ctl = .next)
    (compares : DeadCleanup.CmpOverwrite isem)
    {ρ : Nat → CV} {world : Arm.ArmState} {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    (fault : VAccessTrapFrom sb vc isem ⟨0,0,ρ,world⟩ code property) :
    VAccessTrapFrom sb (DeadCleanup.prune vc) isem ⟨0,0,ρ,world⟩ code property := by
  unfold DeadCleanup.prune
  cases cfg : vc.cfg with
  | error message => exact fault
  | ok graph => exact accessTraps_clean pure compares (DeadCleanup.terminated_of_cfg cfg) fault

/-- The existing prepare validator preserves the actual access operation and address. -/
theorem accessTraps_prepare {sb : Nat} {vc prepared : VCode} {isem : Backend.Proof.Sem}
    (driver : DriverSem isem) (checked : prepCheck vc prepared = true)
    {ρ : Nat → CV} {world : Arm.ArmState} {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    (fault : VAccessTrapFrom sb vc isem ⟨0,0,ρ,world⟩ code property) :
    VAccessTrapFrom sb prepared isem ⟨0,0,ρ,world⟩ code property := by
  unfold prepCheck at checked
  split at checked
  · rename_i successors predecessors successors' predecessors' cfg cfg'
    simp only [Bool.and_eq_true,decide_eq_true_eq] at checked
    obtain ⟨⟨⟨entry,liveEntry⟩,all⟩,rest⟩ := checked
    let live : Nat → Prop := fun b => b < vc.blocks.size ∧ liveOf successors b = true
    have each : ∀ b,live b → ∃ target,sigmaOf vc prepared b = some target ∧
        Driver.keptOk vc prepared successors successors' b target = true ∧
        (successors[b]?.getD #[]).all (fun s => decide (s < vc.blocks.size) && liveOf successors s) = true := by
      intro b ⟨inside,present⟩
      have row := all_range all inside
      rw [present] at row
      simp only [Bool.not_true,Bool.false_or] at row
      split at row
      · cases row
      · rename_i target mapped
        simp only [Bool.and_eq_true] at row
        exact ⟨target,mapped,row.1,row.2⟩
    have kept : ∀ b target,live b → sigmaOf vc prepared b = some target →
        Kept vc prepared successors successors' b target := by
      intro b target alive mapped
      obtain ⟨actual,found,kept,remaining⟩ := each b alive
      rw [mapped] at found
      cases found
      exact keptOk_sound kept
    have nextLive : ∀ (b : Nat) (children : Array Nat) (j child : Nat),live b → successors[b]? = some children → children[j]? = some child → live child := by
      intro b children j child alive found present
      obtain ⟨target,mapped,kept,allChildren⟩ := each b alive
      rw [found,Option.getD_some] at allChildren
      have row := (Array.all_eq_true_iff_forall_mem.mp allChildren) child (Array.mem_of_getElem? present)
      simpa only [Bool.and_eq_true,decide_eq_true_eq] using row
    have initialLive : live 0 := by
      refine ⟨?_,liveEntry⟩
      unfold sigmaOf at entry
      split at entry
      · rename_i block found
        exact (Array.getElem?_eq_some_iff.mp found).1
      · cases entry
    obtain ⟨b,k,regs,next,block,inst,ops,uses,address,bytes,path,found,located,operands,values,access,holds⟩ := fault
    obtain ⟨target,alive,mapped,path'⟩ := prep_star driver cfg cfg' nextLive kept path
      ⟨0,0,ρ,world⟩ ⟨b,k,regs,next⟩ 0 rfl rfl initialLive entry
    obtain ⟨original,block',foundOriginal,found',other1,other2,other3,instructions,other4⟩ := (kept b target alive mapped).blocks
    rw [found] at foundOriginal
    cases foundOriginal
    obtain ⟨inst',at',same⟩ := instructions k inst located
    have unchanged : inst' = inst := by
      rcases same with same | retargeted
      · exact same
      · exact False.elim (access_not_retarget access retargeted)
    subst inst'
    exact ⟨target,k,regs,next,block',inst,ops,uses,address,bytes,path',found',at',operands,values,access,holds⟩
  · cases checked

end Backend.Stock.Proof.MemoryFaults
