import FV.Backend.Proof.StockMemoryAccessRegisterLevel

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-! Preserve stronger trace invariants through the actual access boundary.
The original GoodX variants remain unchanged. -/

theorem realizes_haltAccess_trace {R : RL} {good : Arm.ArmState → Prop} {isem : Backend.Proof.Sem} {sb : Nat}
    {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    (old : Realizes R.vc R.rf isem ckeep R.step (QA R) good) :
    Realizes R.vc R.rf (haltAccess sb code property isem) ckeep R.step (QA R) good := by
  intro s before after related stepped
  cases stepped with
  | move =>
    obtain ⟨n,final,step,held,good⟩ := old s _ _ related .move
    exact ⟨n,final,mstep_congr step (fun _ _ _ _ _ _ _ _ _ impossible => by cases impossible),held,good⟩
  | @op b k allocs items values world block inst operands outs outs' next ctl regs after found located
      valid sizes execution length kept clobbered advance =>
    have step : MStep R.vc (haltAccess sb code property isem) ckeep R.rf
        (.run ⟨b,.op k allocs :: items,values,world⟩) after :=
      MStep.op found located valid sizes execution length kept clobbered advance
    by_cases fault : HaltsAtAccess sb code property inst
        (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world
    · simp only [haltAccess,if_pos fault,Option.some.injEq,Prod.mk.injEq] at execution
      obtain ⟨outsEq,nextEq,controlEq⟩ := execution
      cases controlEq
      cases advance with
      | halt => exact ⟨0,_,step,.inl ⟨trivial,trivial⟩,fun _ impossible => absurd impossible (Nat.not_lt_zero _)⟩
    · have normal : isem inst (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world =
          some (outs,next,ctl) := by simpa only [haltAccess,if_neg fault] using execution
      obtain ⟨n,final,original,held,good⟩ := old s _ _ related
        (MStep.op found located valid sizes normal length kept clobbered advance)
      refine ⟨n,final,mstep_congr original ?_,held,good⟩
      intro b' k' allocs' items' values' world' block' inst' operands' same found' located' valid'
      cases same
      rw [found] at found'
      cases found'
      rw [located] at located'
      cases located'
      rw [valid] at valid'
      cases valid'
      simp only [haltAccess,if_neg fault]


theorem access_allocated_boundary_trace {R : RL} {good : Arm.ArmState → Prop} {isem : Backend.Proof.Sem} {sb : Nat}
    {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (checked : CheckedAt R.vc R.rf cc ins a0)
    (realizes : Realizes R.vc R.rf isem ckeep R.step (QA R) good)
    (initialValues : Loc → CV) (initialRegs : Nat → CV) (world : Arm.ArmState)
    (bindings : Inv ckeep a0 initialValues initialRegs (fun r => initialValues (.reg r)))
    {initial : Arm.ArmState} (entry : QA R initial (MConf.init R.rf initialValues world))
    (fault : VAccessTrapFrom sb R.vc isem ⟨0,0,initialRegs,world⟩ code property) :
    ∃ n b k allocs items values next block inst operands address bytes,
      Q R (iterN R.step n initial) (.run ⟨b,.op k allocs :: items,values,next⟩) ∧
      R.vc.blocks[b]? = some block ∧ block.insts[k]? = some inst ∧ inst.operands = .ok operands ∧
      AccessAt sb inst (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2))
        next code address bytes ∧ property address bytes ∧
      ∀ j < n,good (iterN R.step j initial) := by
  obtain ⟨⟨b,k,regs,next⟩,path,block,inst,operands,found,located,valid,matching,last⟩ := accessTrap_halt fault
  obtain ⟨simulation,relatedInitial,calleeSaved⟩ := checkedAt_sound_match
    (sem := haltAccess sb code property isem) (keep := ckeep) checked initialValues initialRegs world bindings
  have realization := realizes_haltAccess_trace (sb := sb) (code := code) (property := property) realizes
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


theorem access_register_level_boundary_trace {R : RL} {good : Arm.ArmState → Prop} (wellFormed : R.Wf)
    {isem : Backend.Proof.Sem} {sb : Nat} {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (checked : CheckedAt R.vc R.rf cc ins a0)
    (realizes : Realizes R.vc R.rf isem ckeep R.step (QA R) good)
    (initialValues : Loc → CV) (initialRegs : Nat → CV) (world : Arm.ArmState)
    (bindings : Inv ckeep a0 initialValues initialRegs (fun r => initialValues (.reg r)))
    {initial : Arm.ArmState} (entry : QA R initial (MConf.init R.rf initialValues world))
    (fault : VAccessTrapFrom sb R.vc isem ⟨0,0,initialRegs,world⟩ code property)
    (shapes : ∀ (b : Nat) (block : VBlock) (k : Nat) (inst : MInst),R.vc.blocks[b]? = some block → block.insts[k]? = some inst →
      ∀ (uses : List CV) (world : Arm.ArmState) (address : BitVec 64) (bytes : Nat),AccessAt sb inst uses world code address bytes → OrdinaryAccessShape inst)
    (mp : ArmFault.MemMap)
    (unmapped : ∀ address bytes,property address bytes → ∃ k < bytes,mp (address+BitVec.ofNat 64 k) = .none) :
    ∃ n,TrapAtF mp R.fb R.base code (iterN R.step n initial) ∧
      ∀ j < n,good (iterN R.step j initial) := by
  obtain ⟨n,b,k,allocs,items,values,next,block,inst,operands,address,bytes,
    related,found,located,valid,access,property,good⟩ :=
    access_allocated_boundary_trace checked realizes initialValues initialRegs world bindings entry fault
  have missing := unmapped address bytes property
  rcases shapes b block k inst found located _ _ _ _ access with load | store
  · obtain ⟨d,pointer,offset,flags,sourceOffset,rfl⟩ := load
    exact ⟨n,load_unsigned_fault_site wellFormed related found located sourceOffset valid access missing,good⟩
  · obtain ⟨stored,pointer,flags,rfl⟩ := store
    exact ⟨n,store_eight_fault_site wellFormed related found located valid access missing,good⟩

end Backend.Stock.Proof.MemoryFaults
