import FV.Backend.Proof.StockConditionalGuardedLast
import FV.Backend.Proof.StockTermAvailability

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem local_family {b : Clif.Block}
    (family : ∀ stm ∈ b.body,MaskBody.Family stm.inst) : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family stm member with (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  all_goals simp [LocalBody.LocalInst,shape]

private theorem trapped_choice {env : Clif.Env} {cp : Clif.Program} {left : Nat} {t : Clif.State}
    {c : Nat} {yes no : Clif.BlockCall} {code : Clif.TrapCode}
    (empty : t.frame.body = []) (term : t.frame.term = .brif c yes no)
    (trapped : Clif.runLoop env cp left t = .trapped code) :
    ∃ fuel value fr,left = fuel+1 ∧ t.frame.get c = .ok value ∧
      Clif.enterBlock t.frame (if Clif.Sem.truthy value.bits then yes else no) = .ok fr ∧
      Clif.runLoop env cp fuel {t with frame := fr} = .trapped code := by
  cases left with
  | zero => cases trapped
  | succ fuel =>
    rw [Clif.runLoop_succ] at trapped
    simp only [Clif.step,empty,term,Clif.stepTerm] at trapped
    cases read : t.frame.get c with
    | trap readCode =>
      have impossible : t.frame.get c ≠ .trap readCode := by
        intro bad
        unfold Clif.Frame.get Clif.Res.ofOption at bad
        split at bad <;> cases bad
      exact False.elim (impossible read)
    | stuck message => simp only [read,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok value =>
      simp only [read,Clif.StepResult.ofRes] at trapped
      cases crossed : Clif.enterBlock t.frame (if Clif.Sem.truthy value.bits then yes else no) with
      | trap enteredCode => exact False.elim (enterBlock_ne_trap crossed)
      | stuck message => simp only [crossed,Clif.StepResult.ofRes] at trapped; cases trapped
      | ok fr =>
        simp only [crossed,Clif.StepResult.ofRes] at trapped
        exact ⟨fuel,value,fr,rfl,rfl,crossed,trapped⟩

private theorem integer_width {ty : Clif.Ty} {width : Nat}
    (same : CTy.int width = CTy.ofClif ty) : ty.width = width := by
  cases ty <;> simp [CTy.ofClif,Clif.Ty.width] at same ⊢ <;> omega

/-- Original source trapping either executes the first body trap or executes
its actual retained body/parameter branch and preserves the later source trap.
Source fuel, definedness, condition reads, choice and guarded frame are derived. -/
theorem ConditionalBodySpec.trapping_parameter_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (parameter : result.ctx.defInst? c = none)
    (conditionTy : result.ctx.valueType? c = some (.int 32) ∨ result.ctx.valueType? c = some (.int 64))
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ world) :
    TrapRun isem (spec.core.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world code ∨
    ∃ (t : Clif.State) (left : Nat) (value : Clif.Val) (fr : Clif.Frame),
      ∃ index inst ops regs prefixWorld endWorld,
      left+1+b.body.length = fuel ∧ t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
      SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
        (List.range' (blockStart f spec.core.scan.block) b.body.length)
        (0,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧
      t.frame.get c = .ok value ∧
      Clif.enterBlock t.frame (if Clif.Sem.truthy value.bits then yes else no) = .ok fr ∧
      Clif.runLoop env cp left {t with frame := fr} = .trapped code ∧
      SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame ∧
      index+1 = spec.origin.emission.code.size ∧
      seqRun isem (spec.core.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop (spec.body.code.size+index) inst ops regs prefixWorld [] endWorld
          (.goto (if Clif.Sem.truthy value.bits then 0 else 1))) ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
        (b.body.length,t.frame,t.mem) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  have block := spec.split.block
  have originalBlock : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using block
  obtain ⟨otherTerm,otherBody,otherSplit,normal,trapping⟩ := MaskBody.actual_body_refines_at_block
    run scope dominated family spec.events block refines driver stable (env := env) (cp := cp)
  have termEq : spec.term = otherTerm := (List.cons.inj (spec.split.records.symm.trans otherSplit.records)).1
  have buffers := congrArg Array.toList (spec.split.code.symm.trans otherSplit.code)
  rw [termEq] at buffers
  simp only [Array.toList_append] at buffers
  have codeEq : spec.body.code = otherBody.code := Array.toList_inj.mp (List.append_cancel_right buffers)
  rcases LocalBody.actual_local_source_trap_or_continue run spec.events spec.split
      (local_family (family b (List.mem_of_getElem? block)))
      (j := 0) (by omega) (by simpa using remaining) trapped with failed | ⟨t,left,total,continued,empty,steps,frame⟩
  · left
    have failedRun := trapping (0,s.frame,s.mem) code
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using failed) ρ world held
    obtain ⟨offset,inst,ops,regs,prefixWorld,outs,endWorld,execution,coded⟩ := failedRun
    rw [← codeEq] at execution
    refine ⟨offset,inst,ops,regs,prefixWorld,outs,endWorld,?_,coded⟩
    rw [spec.bodyCode,Array.toList_append,List.map_append]
    exact seqRun_append_stop isem execution
  · right
    have tDefined : SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame := by
      apply ArithmeticBody.arithmetic_steps_defined run scope dominated spec.events block
        (env := env) (cp := cp) (s := (0,s.frame,s.mem)) (t := (b.body.length,t.frame,t.mem))
        (j := 0) (n := b.body.length) (by omega) rfl ?_ defined
      simpa only [Nat.add_zero,Nat.sub_zero] using steps
    obtain ⟨middle,bodyWorld,bodyRun,post⟩ := normal (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using steps) ρ world held
    rw [← codeEq] at bodyRun
    rw [← termEq] at post
    have atBranch : t.frame.term = .brif c yes no := frame.2.2.2.trans (atTerm.trans termShape)
    obtain ⟨after,value,fr,leftEq,read,crossed,nextReturned⟩ := trapped_choice empty atBranch continued
    have av0 := buildCtx_term_available spec.build dominated originalBlock c
      (by simp [termShape,abiTerm,Backend.Proof.Driver.termArgs])
    have available : c ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
      simpa only [spec.atBlock] using av0
    have rawGet : t.frame.getAs c value.ty = .ok value.bits := by
      simp [Clif.Frame.getAs,read,Clif.Val.as?]
    have getC := (getAs_congr (fr := t.frame) (ty := value.ty) (restrict_regs_of_mem available)).trans rawGet
    have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
    have width : value.ty.width = 32 ∨ value.ty.width = 64 := by
      rcases conditionTy with narrow | wide
      · have typed : spec.core.scan.ctx.valueType? c = some (.int 32) := by rw [ctxEq]; exact narrow
        exact Or.inl (integer_width (getAs_typed post.2.1 typed getC))
      · have typed : spec.core.scan.ctx.valueType? c = some (.int 64) := by rw [ctxEq]; exact wide
        exact Or.inr (integer_width (getAs_typed post.2.1 typed getC))
    obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,branchRun,branchLast,branchPost,targets,terminal⟩ :=
      spec.parameter_branch_values_last run scope refines stable originalBlock termShape parameter getC width post
    refine ⟨t,after,value,fr,index,inst,ops,regs,prefixWorld,endWorld,?_,empty,frame,?_,read,crossed,
      nextReturned,tDefined,branchLast,?_,branchPost,targets,terminal⟩
    · simpa only [leftEq,Nat.sub_zero] using total
    · simpa only [Nat.add_zero,Nat.sub_zero] using steps
    · rw [spec.bodyCode,Array.toList_append,List.map_append]
      have combined := seqRun_append_fall_stop isem bodyRun branchRun
      by_cases zero : value.bits = 0
      · simpa [List.length_map,Array.length_toList,Clif.Sem.truthy,zero,Nat.add_comm] using combined
      · simpa [List.length_map,Array.length_toList,Clif.Sem.truthy,zero,Nat.add_comm] using combined

end Backend.Stock.Proof.ConditionalValues
