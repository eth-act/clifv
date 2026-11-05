import FV.Backend.Proof.StockTestBitConditionValues
import FV.Backend.Proof.StockNarrow16ConditionCores

/-! Branches on a one-bit condition: source cores and carry cores (#140, CB-13).

`returning/trapping_narrow16_core` (CB-12b) with a one-bit condition (`TestBitCondMetadata`): the
body runs, and the branch uses `test_bit_branch_values_last`, which stops at the `tbnz`/`tbz`.
The branch defines no register (`test_bit_no_defs`), so `branch_carry_of_no_defs` gives the carry
cores `returning/trapping_test_bit_carry_core` (`ReturningCarryCore`, `TrappingCarryCore`). -/

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

private theorem returned_choice {env : Clif.Env} {cp : Clif.Program} {left : Nat} {t : Clif.State}
    {c : Nat} {yes no : Clif.BlockCall} {vals : List Clif.Val} {cm : Clif.Mem}
    (empty : t.frame.body = []) (term : t.frame.term = .brif c yes no)
    (returned : Clif.runLoop env cp left t = .returned vals cm) :
    ∃ fuel value fr,left = fuel+1 ∧ t.frame.get c = .ok value ∧
      Clif.enterBlock t.frame (if Clif.Sem.truthy value.bits then yes else no) = .ok fr ∧
      Clif.runLoop env cp fuel {t with frame := fr} = .returned vals cm := by
  cases left with
  | zero => cases returned
  | succ fuel =>
    rw [Clif.runLoop_succ] at returned
    simp only [Clif.step,empty,term,Clif.stepTerm] at returned
    cases read : t.frame.get c with
    | trap code => simp only [read,Clif.StepResult.ofRes] at returned; cases returned
    | stuck message => simp only [read,Clif.StepResult.ofRes] at returned; cases returned
    | ok value =>
      simp only [read,Clif.StepResult.ofRes] at returned
      cases crossed : Clif.enterBlock t.frame (if Clif.Sem.truthy value.bits then yes else no) with
      | trap code => simp only [crossed,Clif.StepResult.ofRes] at returned; cases returned
      | stuck message => simp only [crossed,Clif.StepResult.ofRes] at returned; cases returned
      | ok fr =>
        simp only [crossed,Clif.StepResult.ofRes] at returned
        exact ⟨fuel,value,fr,rfl,rfl,crossed,returned⟩

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

/-- A successful original source return executes the complete retained scalar body and the
actual `tbnz`/`tbz` branch on a one-bit condition, preserving its source continuation, original
fuel/definedness and guarded frame. The machine stops on the edge of the source truth of the
condition. Source getters, rule selection and machine execution are derived; only source
class metadata is required. -/
theorem ConditionalBodySpec.returning_test_bit_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : TestBitCondMetadata result.ctx c)
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ world) :
    ∃ (t : Clif.State) (left : Nat) (value : Clif.Val) (fr : Clif.Frame),
      ∃ index inst ops regs prefixWorld endWorld,
      left+1+b.body.length = fuel ∧ t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
      SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
        (List.range' (blockStart f spec.core.scan.block) b.body.length)
        (0,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧
      t.frame.get c = .ok value ∧
      Clif.enterBlock t.frame (if Clif.Sem.truthy value.bits then yes else no) = .ok fr ∧
      Clif.runLoop env cp left {t with frame := fr} = .returned vals cm ∧
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
  obtain ⟨t,left,total,continued,empty,steps,frame⟩ := LocalBody.actual_local_source_execution_frame
    run spec.events spec.split (local_family (family b (List.mem_of_getElem? block)))
    (j := 0) (by omega) (by simpa using remaining) returned
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
  obtain ⟨after,value,fr,leftEq,read,crossed,nextReturned⟩ := returned_choice empty atBranch continued
  have av0 := buildCtx_term_available spec.build dominated originalBlock c
    (by simp [termShape,abiTerm,Backend.Proof.Driver.termArgs])
  have available : c ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
    simpa only [spec.atBlock] using av0
  have rawGet : t.frame.getAs c value.ty = .ok value.bits := by
    simp [Clif.Frame.getAs,read,Clif.Val.as?]
  have getC := (getAs_congr (fr := t.frame) (ty := value.ty) (restrict_regs_of_mem available)).trans rawGet
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,branchRun,branchLast,branchPost,targets,terminal⟩ :=
    spec.test_bit_branch_values_last run scope refines stable originalBlock termShape condition getC post
  refine ⟨t,after,value,fr,index,inst,ops,regs,prefixWorld,endWorld,?_,empty,frame,?_,read,crossed,
    nextReturned,tDefined,branchLast,?_,branchPost,targets,terminal⟩
  · simpa only [leftEq,Nat.sub_zero] using total
  · simpa only [Nat.add_zero,Nat.sub_zero] using steps
  · rw [spec.bodyCode,Array.toList_append,List.map_append]
    have combined := seqRun_append_fall_stop isem bodyRun branchRun
    by_cases zero : value.bits = 0
    · simpa [List.length_map,Array.length_toList,Clif.Sem.truthy,zero,Nat.add_comm] using combined
    · simpa [List.length_map,Array.length_toList,Clif.Sem.truthy,zero,Nat.add_comm] using combined

/-- Original source trapping either executes the first body trap or executes its actual retained
body and `tbnz`/`tbz` branch on a one-bit condition and preserves the later source trap. -/
theorem ConditionalBodySpec.trapping_test_bit_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : TestBitCondMetadata result.ctx c)
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
    obtain ⟨after,value,fr,leftEq,read,crossed,nextTrapped⟩ := trapped_choice empty atBranch continued
    have av0 := buildCtx_term_available spec.build dominated originalBlock c
      (by simp [termShape,abiTerm,Backend.Proof.Driver.termArgs])
    have available : c ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
      simpa only [spec.atBlock] using av0
    have rawGet : t.frame.getAs c value.ty = .ok value.bits := by
      simp [Clif.Frame.getAs,read,Clif.Val.as?]
    have getC := (getAs_congr (fr := t.frame) (ty := value.ty) (restrict_regs_of_mem available)).trans rawGet
    obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,branchRun,branchLast,branchPost,targets,terminal⟩ :=
      spec.test_bit_branch_values_last run scope refines stable originalBlock termShape condition getC post
    refine ⟨t,after,value,fr,index,inst,ops,regs,prefixWorld,endWorld,?_,empty,frame,?_,read,crossed,
      nextTrapped,tDefined,branchLast,?_,branchPost,targets,terminal⟩
    · simpa only [leftEq,Nat.sub_zero] using total
    · simpa only [Nat.add_zero,Nat.sub_zero] using steps
    · rw [spec.bodyCode,Array.toList_append,List.map_append]
      have combined := seqRun_append_fall_stop isem bodyRun branchRun
      by_cases zero : value.bits = 0
      · simpa [List.length_map,Array.length_toList,Clif.Sem.truthy,zero,Nat.add_comm] using combined
      · simpa [List.length_map,Array.length_toList,Clif.Sem.truthy,zero,Nat.add_comm] using combined

/-- `returning_test_bit_core` with a carry set: the body and the `tbnz`/`tbz`, which defines no
register, keep `CarryRel` of every set that is available at the block entry. -/
theorem ConditionalBodySpec.returning_test_bit_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : TestBitCondMetadata result.ctx c)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    ReturningCarryCore spec needed fuel s vals cm ρ world := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have noDefs := spec.test_bit_no_defs run scope block termShape condition
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_test_bit_core run scope dominated family refines driver stable termShape condition
      remaining atTerm defined returned held.1
  exact ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,crossed,
    nextReturned,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family refines
      driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- `trapping_test_bit_core` with a carry set. -/
theorem ConditionalBodySpec.trapping_test_bit_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (condition : TestBitCondMetadata result.ctx c)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    TrappingCarryCore spec needed fuel s code ρ world := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have noDefs := spec.test_bit_no_defs run scope block termShape condition
  rcases spec.trapping_test_bit_core run scope dominated family refines driver stable termShape condition
      remaining atTerm defined trapped held.1 with
    failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
      total,empty,frame,steps,read,crossed,nextTrapped,tDefined,last,machine,post,targets,terminal⟩
  · exact Or.inl failed
  · exact Or.inr ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,
      crossed,nextTrapped,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family
        refines driver stable noDefs available steps held machine⟩,targets,terminal⟩

end Backend.Stock.Proof.ConditionalValues
