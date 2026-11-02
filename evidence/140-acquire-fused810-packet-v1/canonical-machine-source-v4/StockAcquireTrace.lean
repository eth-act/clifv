import FV.Backend.Proof.StockAcquireRegisterLevel

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-! Preserve stronger trace invariants through the actual access boundary.
The original GoodX variants remain unchanged. -/

theorem realizes_haltAcquire_trace {R : RL} {good : Arm.ArmState → Prop} {isem : Backend.Proof.Sem} 
    {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    (old : Realizes R.vc R.rf isem ckeep R.step (QA R) good) :
    Realizes R.vc R.rf (haltAcquire code property isem) ckeep R.step (QA R) good := by
  intro s before after related stepped
  cases stepped with
  | move =>
    obtain ⟨n,final,step,held,good⟩ := old s _ _ related .move
    exact ⟨n,final,mstep_congr step (fun _ _ _ _ _ _ _ _ _ impossible => by cases impossible),held,good⟩
  | @op b k allocs items values world block inst operands outs outs' next ctl regs after found located
      valid sizes execution length kept clobbered advance =>
    have step : MStep R.vc (haltAcquire code property isem) ckeep R.rf
        (.run ⟨b,.op k allocs :: items,values,world⟩) after :=
      MStep.op found located valid sizes execution length kept clobbered advance
    by_cases fault : HaltsAtAcquire code property inst
        (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world
    · simp only [haltAcquire,if_pos fault,Option.some.injEq,Prod.mk.injEq] at execution
      obtain ⟨outsEq,nextEq,controlEq⟩ := execution
      cases controlEq
      cases advance with
      | halt => exact ⟨0,_,step,.inl ⟨trivial,trivial⟩,fun _ impossible => absurd impossible (Nat.not_lt_zero _)⟩
    · have normal : isem inst (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world =
          some (outs,next,ctl) := by simpa only [haltAcquire,if_neg fault] using execution
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
      simp only [haltAcquire,if_neg fault]


theorem acquire_allocated_boundary_trace {R : RL} {good : Arm.ArmState → Prop} {isem : Backend.Proof.Sem} 
    {code : Clif.TrapCode} {property : BitVec 64 → Nat → Prop}
    {cc : CheckCtx} {ins : Array (Option AState)} {a0 : AState}
    (checked : CheckedAt R.vc R.rf cc ins a0)
    (realizes : Realizes R.vc R.rf isem ckeep R.step (QA R) good)
    (initialValues : Loc → CV) (initialRegs : Nat → CV) (world : Arm.ArmState)
    (bindings : Inv ckeep a0 initialValues initialRegs (fun r => initialValues (.reg r)))
    {initial : Arm.ArmState} (entry : QA R initial (MConf.init R.rf initialValues world))
    (fault : VAcquireBoundaryFrom R.vc isem ⟨0,0,initialRegs,world⟩ code property) :
    ∃ n b k allocs items values next block inst operands address bytes,
      Q R (iterN R.step n initial) (.run ⟨b,.op k allocs :: items,values,next⟩) ∧
      R.vc.blocks[b]? = some block ∧ block.insts[k]? = some inst ∧ inst.operands = .ok operands ∧
      AcquireAt inst (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2))
        next code address bytes ∧ property address bytes ∧
      ∀ j < n,good (iterN R.step j initial) := by
  obtain ⟨⟨b,k,regs,next⟩,path,block,inst,operands,found,located,valid,matching,last⟩ := acquireTrap_halt fault
  obtain ⟨simulation,relatedInitial,calleeSaved⟩ := checkedAt_sound_match
    (sem := haltAcquire code property isem) (keep := ckeep) checked initialValues initialRegs world bindings
  have realization := realizes_haltAcquire_trace (code := code) (property := property) realizes
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

/-- The checked allocator transfers the exact byte acquire to its linked fault site. -/
theorem acquire_register_level_boundary_from_trace {R : RL} {good : Arm.ArmState → Prop} (wellFormed : R.Wf)
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
          ∃ d pointer flags,inst = .loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags)
    (mp : ArmFault.MemMap)
    (unmapped : ∀ address bytes,property address bytes → ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) :
    ∃ n,TrapAtF mp R.fb R.base code (iterN R.step n initial) ∧
      ∀ j < n,good (iterN R.step j initial) := by
  obtain ⟨n,b,k,allocs,items,values,next,block,inst,operands,address,bytes,
    related,found,located,valid,access,property,good⟩ :=
    acquire_allocated_boundary_trace checked realizes initialValues initialRegs world bindings entry fault
  obtain ⟨d,pointer,flags,rfl⟩ := shapes b block k inst found located _ _ _ _ access
  exact ⟨n,acquire_byte_fault_site wellFormed related found located valid access (unmapped _ _ property),good⟩

end Backend.Stock.Proof.Acquire810
