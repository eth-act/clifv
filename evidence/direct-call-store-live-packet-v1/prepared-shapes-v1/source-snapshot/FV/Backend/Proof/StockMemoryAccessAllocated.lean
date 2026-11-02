import FV.Backend.Proof.StockMemoryAccessRealizes
import FV.E2E.RegLevelCorrectU

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The checked allocator reaches the actual access item with the same operand values.
The proof derives its cursor and source-to-location binding from the landed simulation. -/
theorem access_allocated_boundary {R : RL} {isem : Backend.Proof.Sem} {sb : Nat}
    {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (checked : CheckedAt R.vc R.rf cc ins a0)
    (realizes : Realizes R.vc R.rf isem ckeep R.step (QA R) R.GoodX)
    (initialValues : Loc → CV) (initialRegs : Nat → CV) (world : Arm.ArmState)
    (bindings : Inv ckeep a0 initialValues initialRegs (fun r => initialValues (.reg r)))
    {initial : Arm.ArmState} (entry : QA R initial (MConf.init R.rf initialValues world))
    (fault : VAccessTrapFrom sb R.vc isem ⟨0,0,initialRegs,world⟩ code property) :
    ∃ n b k allocs items values next block inst operands address bytes,
      Q R (iterN R.step n initial) (.run ⟨b,.op k allocs :: items,values,next⟩) ∧
      R.vc.blocks[b]? = some block ∧ block.insts[k]? = some inst ∧ inst.operands = .ok operands ∧
      AccessAt sb inst (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2))
        next code address bytes ∧ property address bytes ∧
      ∀ j < n,R.GoodX (iterN R.step j initial) := by
  obtain ⟨⟨b,k,regs,next⟩,path,block,inst,operands,found,located,valid,matching,last⟩ := accessTrap_halt fault
  obtain ⟨simulation,relatedInitial,calleeSaved⟩ := checkedAt_sound_match
    (sem := haltAccess sb code property isem) (keep := ckeep) checked initialValues initialRegs world bindings
  have realization := realizes_haltAccess (sb := sb) (code := code) (property := property) realizes
  obtain ⟨n1,current,held,related,good1⟩ := forward simulation realization path relatedInitial entry
  obtain ⟨n2,before,after,held2,related2,stepped,related3,good2⟩ :=
    forward_last simulation realization last _ current _ (Nat.le_refl _) related held
  cases stepped with
  | move => obtain ⟨state,impossible⟩ := simulation.run related3; cases impossible
  | @op b' k' allocs items values world' block' inst' operands' outs outs' final ctl stored result
      found' located' valid' sizes execution length kept clobbered advance =>
    obtain ⟨sameBlock,sameIndex,sameWorld⟩ := simulation.at_op related2
    simp only at sameBlock sameIndex sameWorld
    subst sameBlock sameIndex sameWorld
    rw [found] at found'
    cases found'
    rw [located] at located'
    cases located'
    rw [valid] at valid'
    cases valid'
    have uses := matchRun_uses checked related2
      (MStep.op found located valid sizes execution length kept clobbered advance) found located valid
    obtain ⟨address,bytes,access,property⟩ := matching
    have nonreturn : ∀ returns,inst ≠ .rets returns := by
      intro returns impossible
      cases impossible
      cases access
    have actual := (qa_op held2 found located nonreturn).1
    refine ⟨n1+n2,b,k,allocs,items,values,next,block,inst,operands,address,bytes,?_,
      found,located,valid,?_,property,?_⟩
    · simpa only [iterN_add] using actual
    · rw [uses]
      exact access
    · exact trace_add good1 good2

end Backend.Stock.Proof.MemoryFaults
