import FV.Backend.Proof.StockTableBranchValues
import FV.Backend.Proof.StockBranchLabelsCarry
import FV.Backend.Proof.StockParameterLoopReturn
import FV.Backend.Proof.StockParameterLoopTrap
import FV.Backend.Proof.StockSelectedRouteExecution

/-! `br_table` blocks with carry sets (#140, CB-14b).

A `br_table x dc tbl` block on an `i32` index, with fewer than 4096 table entries, composes below
the fuel with any block arguments on its successors.

* The carry cores `TableBodySpec.returning/trapping_table_carry_core`: the body keeps `CarryRel`
  (`scalar_body_carry_refines`), the source takes the `br_table` edge `branchIdx` of the index, and
  the resolved emission stops at its `jt_sequence` on the same edge
  (`table_branch_values_last`). The `jt_sequence` writes its two temporaries after the stop; the
  register update keeps the guarded frame and the carried values
  (`guarded_of_table_update`, `table_carry_of_update`). The cores state the edge as a selected
  destination index of the terminator (`ReturningTableCarryCore`, `TrappingTableCarryCore`).
* The successors: `selected_arguments_demanded_of_labels` and
  `selected_argument_values_of_labels` for the list `d :: ts` of successor labels
  (`TableBodySpec.selected_arguments_demanded`, `TableBodySpec.selected_argument_values`): the
  outgoing collection over all successors marks the arguments of each original successor
  (`collect_marks`), and a critical edge marks them before its predecessor is scanned.
* The actual copy route runs from the register update at the stop
  (`SelectedCopyRoute.execute_update`), so the selected successor continues below the fuel
  (`TableBodySpec.returning/trapping_selected_table_carry_below`). -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Backend.Stock.Proof.TableBranch
  Backend.Stock.Proof.LoopCarry Backend.Stock.Proof.Control
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem local_family {b : Clif.Block}
    (family : ∀ stm ∈ b.body,MaskBody.Family stm.inst) : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
  intro stm member
  rcases family stm member with (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
  all_goals simp [LocalBody.LocalInst,shape]

private theorem returned_table_choice {env : Clif.Env} {cp : Clif.Program} {left : Nat} {t : Clif.State}
    {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall} {vals : List Clif.Val} {cm : Clif.Mem}
    (empty : t.frame.body = []) (term : t.frame.term = .brTable x dc tbl)
    (returned : Clif.runLoop env cp left t = .returned vals cm) :
    ∃ fuel value fr,left = fuel+1 ∧ t.frame.get x = .ok value ∧
      Clif.enterBlock t.frame (tbl[value.toNat]?.getD dc) = .ok fr ∧
      Clif.runLoop env cp fuel {t with frame := fr} = .returned vals cm := by
  cases left with
  | zero => cases returned
  | succ fuel =>
    rw [Clif.runLoop_succ] at returned
    simp only [Clif.step,empty,term,Clif.stepTerm] at returned
    cases read : t.frame.get x with
    | trap code => simp only [read,Clif.StepResult.ofRes] at returned; cases returned
    | stuck message => simp only [read,Clif.StepResult.ofRes] at returned; cases returned
    | ok value =>
      simp only [read,Clif.StepResult.ofRes] at returned
      cases crossed : Clif.enterBlock t.frame (tbl[value.toNat]?.getD dc) with
      | trap code => simp only [crossed,Clif.StepResult.ofRes] at returned; cases returned
      | stuck message => simp only [crossed,Clif.StepResult.ofRes] at returned; cases returned
      | ok fr =>
        simp only [crossed,Clif.StepResult.ofRes] at returned
        exact ⟨fuel,value,fr,rfl,rfl,crossed,returned⟩

private theorem trapped_table_choice {env : Clif.Env} {cp : Clif.Program} {left : Nat} {t : Clif.State}
    {x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall} {code : Clif.TrapCode}
    (empty : t.frame.body = []) (term : t.frame.term = .brTable x dc tbl)
    (trapped : Clif.runLoop env cp left t = .trapped code) :
    ∃ fuel value fr,left = fuel+1 ∧ t.frame.get x = .ok value ∧
      Clif.enterBlock t.frame (tbl[value.toNat]?.getD dc) = .ok fr ∧
      Clif.runLoop env cp fuel {t with frame := fr} = .trapped code := by
  cases left with
  | zero => cases trapped
  | succ fuel =>
    rw [Clif.runLoop_succ] at trapped
    simp only [Clif.step,empty,term,Clif.stepTerm] at trapped
    cases read : t.frame.get x with
    | trap readCode =>
      have impossible : t.frame.get x ≠ .trap readCode := by
        intro bad
        unfold Clif.Frame.get Clif.Res.ofOption at bad
        split at bad <;> cases bad
      exact False.elim (impossible read)
    | stuck message => simp only [read,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok value =>
      simp only [read,Clif.StepResult.ofRes] at trapped
      cases crossed : Clif.enterBlock t.frame (tbl[value.toNat]?.getD dc) with
      | trap enteredCode => exact False.elim (enterBlock_ne_trap crossed)
      | stuck message => simp only [crossed,Clif.StepResult.ofRes] at trapped; cases trapped
      | ok fr =>
        simp only [crossed,Clif.StepResult.ofRes] at trapped
        exact ⟨fuel,value,fr,rfl,rfl,crossed,trapped⟩

/-- The `branchIdx` edge of a `br_table` selects the source successor of the index. -/
theorem table_dests_target (x : Nat) (dc : Clif.BlockCall) (tbl : List Clif.BlockCall) (v : Nat) :
    (dests (.brTable x dc tbl))[tableTarget v tbl.length]? = some (tbl[v]?.getD dc) := by
  unfold tableTarget
  split
  · rename_i inside
    simp [dests,List.getElem?_eq_getElem inside]
  · rename_i outside
    simp [dests,List.getElem?_eq_none (Nat.le_of_not_lt outside)]

/-- The conclusion of `returning_table_carry_core`: the source runs the body and the `br_table`,
then returns from the selected successor `bc` at destination index `choice` with `left` fuel; the
actual core code stops at the emission's last instruction on the edge `choice`, and the register
update of the stop holds `CarryRel` of `needed` at the block's end. -/
def ReturningTableCarryCore {f : Clif.Function} {result : Result} {b : Clif.Block} {label bi x : Nat}
    {dc : Clif.BlockCall} {tbl : List Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (needed : Nat → Prop) (fuel : Nat) (s : Clif.State) (vals : List Clif.Val) (cm : Clif.Mem)
    (ρ : Nat → CV) (world : Arm.ArmState) : Prop :=
  ∃ (t : Clif.State) (left : Nat) (fr : Clif.Frame) (choice : Nat) (bc : Clif.BlockCall),
    ∃ index inst ops regs prefixWorld outs endWorld,
    left+1+b.body.length = fuel ∧ t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
    SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (List.range' (blockStart f spec.core.scan.block) b.body.length)
      (0,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧
    (dests b.term)[choice]? = some bc ∧ Clif.enterBlock t.frame bc = .ok fr ∧
    Clif.runLoop env cp left {t with frame := fr} = .returned vals cm ∧
    SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame ∧
    index+1 = spec.origin.emission.code.size ∧
    seqRun isem (spec.core.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop (spec.body.code.size+index) inst ops regs prefixWorld outs endWorld (.goto choice)) ∧
    Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
      (b.body.length,t.frame,t.mem) (vdefUpd ops outs regs) endWorld ∧
    inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true

/-- The conclusion of `trapping_table_carry_core`: the actual core code traps in the body, or
`ReturningTableCarryCore` with a later source trap in place of the return. -/
def TrappingTableCarryCore {f : Clif.Function} {result : Result} {b : Clif.Block} {label bi x : Nat}
    {dc : Clif.BlockCall} {tbl : List Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (needed : Nat → Prop) (fuel : Nat) (s : Clif.State) (code : Clif.TrapCode)
    (ρ : Nat → CV) (world : Arm.ArmState) : Prop :=
  TrapRun isem (spec.core.code.toList.map
    (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world code ∨
  ∃ (t : Clif.State) (left : Nat) (fr : Clif.Frame) (choice : Nat) (bc : Clif.BlockCall),
    ∃ index inst ops regs prefixWorld outs endWorld,
    left+1+b.body.length = fuel ∧ t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
    SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (List.range' (blockStart f spec.core.scan.block) b.body.length)
      (0,s.frame,s.mem) (b.body.length,t.frame,t.mem) ∧
    (dests b.term)[choice]? = some bc ∧ Clif.enterBlock t.frame bc = .ok fr ∧
    Clif.runLoop env cp left {t with frame := fr} = .trapped code ∧
    SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame ∧
    index+1 = spec.origin.emission.code.size ∧
    seqRun isem (spec.core.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop (spec.body.code.size+index) inst ops regs prefixWorld outs endWorld (.goto choice)) ∧
    Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
      (b.body.length,t.frame,t.mem) (vdefUpd ops outs regs) endWorld ∧
    inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true

/-- The branch step of a table core: from the source state `t` at the `br_table`, with a body run
to `middle` and `CarryRel` of `needed` there, the index read, the selected edge and the stopped
emission, with the carry at the register update of the stop. -/
private theorem table_branch_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : tbl.length < 4096)
    {needed : Nat → Prop}
    (available : ∀ y,needed y → y ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {t : Clif.State} {value : Clif.Val} (read : t.frame.get x = .ok value)
    {middle : Nat → CV} {bodyWorld : Arm.ArmState}
    (post : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
      (b.body.length,t.frame,t.mem) middle bodyWorld) :
    ∃ index inst ops prefixWorld outs endWorld,
      (dests b.term)[tableTarget value.toNat tbl.length]? = some (tbl[value.toNat]?.getD dc) ∧
      index+1 = spec.origin.emission.code.size ∧
      seqRun isem (spec.origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) middle bodyWorld =
        some (.stop index inst ops middle prefixWorld outs endWorld (.goto (tableTarget value.toNat tbl.length))) ∧
      Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
        (b.body.length,t.frame,t.mem) (vdefUpd ops outs middle) endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  have block : f.blocks[bi]? = some b := by simpa only [spec.atBlock] using spec.split.block
  have count := table_successor_count run scope tag block termShape
  have successorsSmall : result.order.successors[label]!.size ≤ 4096 := by omega
  have av0 := buildCtx_term_available spec.build dominated block x
    (by simp [termShape,abiTerm,Backend.Proof.Driver.termArgs])
  have availableX : x ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
    simpa only [spec.atBlock] using av0
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have typeHere : spec.core.scan.ctx.valueType? x = some (.int 32) := by rw [ctxEq]; exact typeX
  have regsX : t.frame.regs x = some value := by
    cases found : t.frame.regs x with
    | none => simp [Clif.Frame.get,found] at read
    | some v =>
      simp only [Clif.Frame.get,found,Clif.Res.ofOption,Clif.Res.ok.injEq] at read
      rw [read]
  have typedValue : CTy.ofClif value.ty = .int 32 :=
    post.1.2.1.2 x (.int 32) value typeHere (by rw [restrict_regs_of_mem availableX]; exact regsX)
  obtain ⟨vty,vbits⟩ := value
  have tyEq : vty = .i32 := by
    cases vty <;> first | rfl | (exfalso; simp [CTy.ofClif] at typedValue)
  subst tyEq
  have rawGet : t.frame.getAs x .i32 = .ok vbits := by
    simp [Clif.Frame.getAs,read,Clif.Val.as?]
  have getX := (getAs_congr (fr := t.frame) (ty := .i32) (restrict_regs_of_mem availableX)).trans rawGet
  obtain ⟨d,ts,labels,frontier,defs,index,inst,ops,prefixWorld,outs,endWorld,branchRun,branchLast,branchPost,
    targets,terminal⟩ := spec.table_branch_values_last run scope dominated refines stable tag block termShape
      typeX successorsSmall getX post.1
  have tsLength : ts.length = tbl.length := by
    have lengths := congrArg List.length labels
    simp only [Array.length_toList,List.length_cons,count] at lengths
    omega
  rw [tsLength] at branchRun
  have updateFrame := spec.table_stop_update_frame run scope dominated tag termShape typeX successorsSmall defs branchRun
  have choiceSel := table_dests_target x dc tbl vbits.toNat
  rw [← termShape] at choiceSel
  exact ⟨index,inst,ops,prefixWorld,outs,endWorld,choiceSel,branchLast,branchRun,
    ⟨spec.guarded_of_table_update run scope dominated tag termShape typeX successorsSmall branchPost updateFrame,
      spec.table_carry_of_update run scope dominated tag termShape typeX successorsSmall available post.2 updateFrame⟩,
    targets,terminal⟩

/-- **The carry return core of a `br_table` block.** A successful original source return
executes the complete retained scalar body and the actual `br_table` emission on an `i32` index,
with fewer than 4096 table entries. The machine stops at the `jt_sequence` on the edge of the
source index; the register update of the stop keeps `CarryRel` of every set that is available at
the block entry. -/
theorem TableBodySpec.returning_table_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : tbl.length < 4096)
    {needed : Nat → Prop}
    (available : ∀ y,needed y → y ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    ReturningTableCarryCore spec needed fuel s vals cm ρ world := by
  have block := spec.split.block
  obtain ⟨t,left,total,continued,empty,steps,frame⟩ := LocalBody.actual_local_source_execution_frame
    run spec.events spec.split (local_family (family b (List.mem_of_getElem? block)))
    (j := 0) (by omega) (by simpa using remaining) returned
  have tDefined : SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame := by
    apply ArithmeticBody.arithmetic_steps_defined run scope dominated spec.events block
      (env := env) (cp := cp) (s := (0,s.frame,s.mem)) (t := (b.body.length,t.frame,t.mem))
      (j := 0) (n := b.body.length) (by omega) rfl ?_ defined
    simpa only [Nat.add_zero,Nat.sub_zero] using steps
  have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    exact MaskBody.family_formats (family block member stm present)
  obtain ⟨middle,bodyWorld,bodyRun,post⟩ := (Inherited.scalar_body_carry_refines run scope dominated spec.events
    spec.split formats (family b (List.mem_of_getElem? block)) available refines driver stable
    (env := env) (cp := cp)).1 (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse]
      using steps)
    ρ world (by simpa only [spec.split.state] using held)
  have atTable : t.frame.term = .brTable x dc tbl := frame.2.2.2.trans (atTerm.trans termShape)
  obtain ⟨after,value,fr,leftEq,read,crossed,nextReturned⟩ := returned_table_choice empty atTable continued
  obtain ⟨index,inst,ops,prefixWorld,outs,endWorld,selected,last,branchRun,carried,targets,terminal⟩ :=
    table_branch_step run scope dominated refines stable spec tag termShape typeX small available read post
  refine ⟨t,after,fr,_,_,index,inst,ops,middle,prefixWorld,outs,endWorld,?_,empty,frame,?_,selected,crossed,
    nextReturned,tDefined,last,?_,carried,targets,terminal⟩
  · simpa only [leftEq,Nat.sub_zero] using total
  · simpa only [Nat.add_zero,Nat.sub_zero] using steps
  · rw [spec.bodyCode,Array.toList_append,List.map_append]
    have combined := seqRun_append_fall_stop isem bodyRun branchRun
    simpa [List.length_map,Array.length_toList,Nat.add_comm] using combined

/-- **The carry first-trap core of a `br_table` block.** Original source trapping either executes
the first body trap or executes the retained body and `br_table` emission and preserves the later
source trap. -/
theorem TableBodySpec.trapping_table_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : tbl.length < 4096)
    {needed : Nat → Prop}
    (available : ∀ y,needed y → y ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    TrappingTableCarryCore spec needed fuel s code ρ world := by
  have block := spec.split.block
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
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using failed) ρ world held.1
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
    have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
      intro block member stm present
      exact MaskBody.family_formats (family block member stm present)
    obtain ⟨middle,bodyWorld,bodyRun,post⟩ := (Inherited.scalar_body_carry_refines run scope dominated spec.events
      spec.split formats (family b (List.mem_of_getElem? block)) available refines driver stable
      (env := env) (cp := cp)).1 (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse]
        using steps)
      ρ world (by simpa only [spec.split.state] using held)
    have atTable : t.frame.term = .brTable x dc tbl := frame.2.2.2.trans (atTerm.trans termShape)
    obtain ⟨after,value,fr,leftEq,read,crossed,nextTrapped⟩ := trapped_table_choice empty atTable continued
    obtain ⟨index,inst,ops,prefixWorld,outs,endWorld,selected,last,branchRun,carried,targets,terminal⟩ :=
      table_branch_step run scope dominated refines stable spec tag termShape typeX small available read post
    refine ⟨t,after,fr,_,_,index,inst,ops,middle,prefixWorld,outs,endWorld,?_,empty,frame,?_,selected,crossed,
      nextTrapped,tDefined,last,?_,carried,targets,terminal⟩
    · simpa only [leftEq,Nat.sub_zero] using total
    · simpa only [Nat.add_zero,Nat.sub_zero] using steps
    · rw [spec.bodyCode,Array.toList_append,List.map_append]
      have combined := seqRun_append_fall_stop isem bodyRun branchRun
      simpa [List.length_map,Array.length_toList,Nat.add_comm] using combined

/-! ## The successors of a table -/

private theorem marks_size (xs : List Nat) (st : State) :
    (xs.foldl State.mark st).demand.size = st.demand.size := by
  induction xs generalizing st with
  | nil => rfl
  | cons x xs ih =>
    simpa only [List.foldl_cons,State.mark,Array.size_modify] using ih (st.mark x)

private theorem mapped_member {ctx : Ctx} {xs : List Nat} {rs : List Reg}
    (mapped : xs.mapM ctx.valueReg? = some rs) {x : Nat} (member : x ∈ xs) :
    ∃ r,ctx.valueReg? x = some r := by
  induction xs generalizing rs with
  | nil => cases member
  | cons y ys ih =>
    simp only [List.mapM_cons,Option.bind_eq_bind,Option.bind_eq_some_iff,
      Option.pure_def,Option.some.injEq] at mapped
    obtain ⟨r,lookup,tail,rest,rfl⟩ := mapped
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨r,lookup⟩
    · exact ih rest member

private theorem view_avail {ctx original : Ctx}
    (view : DFGViewEq ctx original) (f : Clif.Function) :
    availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs,Ctx.defInst?,view.valDef,view.insts]
  have users : fUsers ctx = fUsers original := by
    simp only [fUsers,usersN,args,view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by
    unfold fInB0
    rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0,view.valDef,bytes,args]
  simp only [availIn,inFix_eq,users,bytes,work,view.valDef]

/-- One outgoing collection step for a branch successor at an original node marks the selected
arguments; at an edge node it changes nothing. -/
private theorem outgoing_step_marks {ctx : Ctx} {f : Clif.Function} (func : ctx.func = f)
    {bi : Nat} {b : Clif.Block} (source : f.blocks[bi]? = some b) {order : Order}
    {label j : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[j]? = some bc)
    {input next : State} {acc acc' : Array (Array Reg)}
    (run : outgoingStep ctx order bi (input,acc) (label,j) = .ok (next,acc')) :
    (∀ t,order.nodes[label]! = .original t → next = bc.args.foldl State.mark input ∧
      ∃ regs : List Reg,bc.args.mapM ctx.valueReg? = some regs) ∧
      (next = input ∨ next = bc.args.foldl State.mark input) := by
  unfold outgoingStep at run
  cases node : order.nodes[label]! with
  | edge pred k target =>
    simp only [node,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at run
    refine ⟨fun t same => (by cases same),Or.inl run.1.symm⟩
  | original t =>
    simp only [node] at run
    cases call : branchArgs ctx input bi j with
    | error message => simp only [call,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨args,state⟩ := pair
      simp only [call,bind,Except.bind,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at run
      obtain ⟨rfl,-⟩ := run
      have marked := stock_branchArgs_selected_marks func source selected call
      exact ⟨fun _ _ => ⟨marked,args.toList,stock_branchArgs_selected_mapping func source selected call⟩,
        Or.inr marked⟩

/-- **The outgoing collection over any list of successors marks the arguments of each original
successor.** The demand array keeps its size, earlier demands stay demanded, and every argument
of a successor at an original node is demanded at the end. -/
theorem collect_marks {ctx : Ctx} {f : Clif.Function} (func : ctx.func = f)
    {bi : Nat} {b : Clif.Block} (source : f.blocks[bi]? = some b) {order : Order} :
    ∀ (pairs : List (Nat × Nat)) (input next : State) (acc acc' : Array (Array Reg)),
    (∀ p ∈ pairs,∃ bc,(dests b.term)[p.2]? = some bc) →
    pairs.foldlM (outgoingStep ctx order bi) (input,acc) = .ok (next,acc') →
    next.demand.size = input.demand.size ∧
    (∀ x,x < input.demand.size → Demanded input x → Demanded next x) ∧
    ∀ p ∈ pairs,∀ (bc : Clif.BlockCall) (t : Nat),(dests b.term)[p.2]? = some bc →
      order.nodes[p.1]! = .original t →
      (∃ regs : List Reg,bc.args.mapM ctx.valueReg? = some regs) ∧
      ∀ x ∈ bc.args,x < input.demand.size → Demanded next x := by
  intro pairs
  induction pairs with
  | nil =>
    intro input next acc acc' _ run
    simp only [List.foldlM_nil,pure,Except.pure,Except.ok.injEq,Prod.mk.injEq] at run
    obtain ⟨rfl,-⟩ := run
    exact ⟨rfl,fun _ _ demanded => demanded,fun p member => by cases member⟩
  | cons p rest ih =>
    intro input next acc acc' every run
    obtain ⟨label,j⟩ := p
    rw [List.foldlM_cons] at run
    cases step : outgoingStep ctx order bi (input,acc) (label,j) with
    | error message => simp only [step,bind,Except.bind] at run; cases run
    | ok pair =>
      obtain ⟨middle,accm⟩ := pair
      simp only [step,bind,Except.bind] at run
      obtain ⟨bc0,selected0⟩ := every (label,j) (List.mem_cons_self ..)
      obtain ⟨original,either⟩ := outgoing_step_marks func source selected0 step
      obtain ⟨sizeRest,monoRest,marksRest⟩ :=
        ih middle next accm acc' (fun q member => every q (List.mem_cons_of_mem _ member)) run
      have middleSize : middle.demand.size = input.demand.size := by
        rcases either with same | same <;> simp only [same,marks_size]
      refine ⟨sizeRest.trans middleSize,?_,?_⟩
      · intro x bound demanded
        have middleBound : x < middle.demand.size := by rw [middleSize]; exact bound
        apply monoRest x middleBound
        rcases either with same | same
        · rw [same]; exact demanded
        · rw [same]; exact (demanded_markList_iff _ _ x bound).mpr (Or.inr demanded)
      · intro q member bc t selected node
        rcases List.mem_cons.mp member with rfl | later
        · have same : bc = bc0 := Option.some.inj (selected.symm.trans selected0)
          subst same
          obtain ⟨marked,mapping⟩ := original t node
          refine ⟨mapping,?_⟩
          intro x inside bound
          have middleBound : x < middle.demand.size := by rw [middleSize]; exact bound
          apply monoRest x middleBound
          rw [marked]
          exact (demanded_markList_iff _ _ x bound).mpr (Or.inl inside)
        · obtain ⟨mapping,demanded⟩ := marksRest q later bc t selected node
          refine ⟨mapping,?_⟩
          intro x inside bound
          have middleBound : x < middle.demand.size := by rw [middleSize]; exact bound
          exact demanded x inside middleBound

/-- `selected_arguments_demanded_of_labels` for the successors `d :: ts` of a `br_table`: every
source argument of a selected successor is demanded after the body, at an original or a
critical-edge successor. -/
theorem TableBodySpec.selected_arguments_demanded {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brTable x dc tbl)
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc)
    {y : Nat} (member : y ∈ bc.args) : Demanded spec.term.output.state y := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  have func := (buildCtx_mappedInv scope spec.build).func
  have terminal : spec.term ∈ spec.core.scan.output.records := by
    rw [spec.split.records]
    exact List.mem_cons_self ..
  have recordSize := Extent.lower_record_demand_size run spec.core.scan spec.events spec.term terminal
  obtain ⟨tl,targetLabel,lookup,nonentry,successor,node⟩ :=
    stock_lower_selected_successor run scope tag source selected
  have inBounds : ∀ (regs : List Reg),bc.args.mapM result.ctx.valueReg? = some regs →
      y < result.ctx.valTy.size := by
    intro regs mapping
    obtain ⟨r,mapped⟩ := mapped_member mapping member
    have currentMap : spec.core.scan.ctx.valueReg? y = some r := by
      rw [(stock_lower_record_context run scope spec.events).2.1 y]
      exact mapped
    have bound := (Extent.lower_mapped_demand_bounds run scope spec.events terminal currentMap).1
    rw [recordSize.1] at bound
    exact bound
  rcases node with original | edge
  · obtain ⟨emission,afterEdges,_,_,outgoing,scanInput,_,branchFlag,_⟩ :=
      table_core_calls term spec.coreRun
    unfold collectOutgoing at outgoing
    have count := table_successor_count run scope tag source term
    have every : ∀ p ∈ result.order.successors[label]!.zipIdx.toList,∃ bc,(dests b.term)[p.2]? = some bc := by
      intro p inside
      rw [Array.toList_zipIdx] at inside
      have found := List.mk_mem_zipIdx_iff_getElem?.mp (show (p.1,p.2) ∈ _ from inside)
      have bound := (List.getElem?_eq_some_iff.mp found).1
      simp only [Array.length_toList,count] at bound
      refine ⟨(dc :: tbl)[p.2]'(by simpa using bound),?_⟩
      simp only [term,dests]
      exact List.getElem?_eq_getElem _
    obtain ⟨sizeAfter,_,marks⟩ := collect_marks func source _ _ _ _ _ every outgoing
    have pairMember : (targetLabel,index) ∈ result.order.successors[label]!.zipIdx.toList := by
      rw [Array.toList_zipIdx]
      exact List.mk_mem_zipIdx_iff_getElem?.mpr (by simpa only [Array.getElem?_toList] using successor)
    have nodeTag : result.order.nodes[targetLabel]! = .original tl := by simp [getElem!_def,original]
    obtain ⟨⟨regs,mapping⟩,demanded⟩ := marks _ pairMember bc tl selected nodeTag
    have outputDemand := (stock_branch_scan_body_code spec.split branchFlag).2
    have afterSize : afterEdges.demand.size = result.ctx.valTy.size := by
      have := recordSize.1
      rw [spec.split.termInput,scanInput] at this
      exact this
    have bound := inBounds regs mapping
    have emissionBound : y < emission.state.demand.size := by
      rw [← sizeAfter,afterSize]
      exact bound
    have demandedAfter : Demanded afterEdges y := demanded y member emissionBound
    unfold Demanded at demandedAfter ⊢
    rw [outputDemand,spec.split.termInput,scanInput]
    exact demandedAfter
  · have later := stock_lower_edge_after_pred run scope tag edge
    have bounded := (Array.getElem?_eq_some_iff.mp edge).1
    have edgeTag : result.order.nodes[targetLabel]! = .edge bi index tl := by simp [getElem!_def,edge]
    have secondTag : result.order.nodes[label]! = .original spec.core.scan.block := by
      simp [getElem!_def,tag,spec.atBlock]
    obtain ⟨input,size,⟨regs,mapping⟩,flow⟩ := ordered_edge_demand_of_labels run scope bounded later
      edgeTag secondTag spec.events spec.split source selected
    have bound : y < input.demand.size := by rw [size]; exact inBounds regs mapping
    have marked := (demanded_markList_iff input bc.args y bound).mpr (Or.inl member)
    unfold Demanded at marked ⊢
    have := flow y
    omega

/-- `selected_argument_values_of_labels` for a `br_table`: a guarded post-body frame holds the
source arguments of a selected successor, at an original or a critical-edge successor. -/
theorem TableBodySpec.selected_argument_values {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (term : b.term = .brTable x dc tbl)
    {fr : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ w)
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc) :
    ValuesHeld (fun y => y ∈ bc.args) result.ctx fr (fun k => ρ (aliasNum result.final.alias k)) := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  obtain ⟨original,st0,oldBuild,_,view⟩ := buildCtx_source spec.build
  have choice : bc ∈ dc :: tbl := by simpa [term,dests] using List.mem_of_getElem? selected
  intro y member v read
  have inArgs : y ∈ Driver.termArgs (abiTerm f b.term) := by
    rcases List.mem_cons.mp choice with same | inTable
    · subst same
      simp only [term,abiTerm,Driver.termArgs,List.mem_cons,List.mem_append,member,true_or,or_true]
    · have inFlat : y ∈ tbl.flatMap (·.args) := List.mem_flatMap.mpr ⟨bc,inTable,member⟩
      simp only [term,abiTerm,Driver.termArgs,List.mem_cons,List.mem_append,inFlat,true_or,or_true]
  have available := (dominated.uses original spec.ranges st0 oldBuild bi b source).2 y inArgs
  have available' : y ∈ availOf f (availIn f result.ctx) spec.core.scan.block b.body.length := by
    rw [spec.atBlock,view_avail view f]
    exact available
  obtain ⟨n,mapped,value⟩ := held.2.2.2 y
    ⟨spec.selected_arguments_demanded run scope tag term selected member,available'⟩ v read
  refine ⟨n,?_,value⟩
  rw [← (stock_lower_record_context run scope spec.events).2.1 y]
  exact mapped

/-- `selected_successor_carry` for a `br_table`: the predecessor holds `carry` at its end, the
successor needs its scan demand and `carried`, and `EdgeCover` replaces the demand order. -/
theorem TableBodySpec.selected_successor_carry
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    {index : Nat} {bc : Clif.BlockCall} (selected : (dests b.term)[index]? = some bc)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList)
    (nextBlock : next.block = sourceTargetIndex f bc)
    {carry carried : Nat → Prop}
    (carriedAvailable : ∀ y,carried y → y ∈ availOf f (availIn f result.ctx) next.block 0)
    (cover : EdgeCover f result next.block (sourceTargetParams f bc) next.output.state carried
      spec.term.output.state carry)
    {fr fr' : Clif.Frame} {cm : Clif.Mem} {ρ : Nat → CV} {w : Arm.ArmState}
    (before : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.term.output.state (b.body.length,fr,cm) ρ w)
    (defined : SourceDefinedAt f result.ctx bi b.body.length fr)
    (entered : Clif.enterBlock fr bc = .ok fr')
    (arguments : ValuesHeld (fun y => y ∈ bc.args) result.ctx fr
      (fun key => ρ (aliasNum result.final.alias key))) :
    ∃ tl targetLabel ρ',blockIdx? f bc.block = some tl ∧
      result.order.nodes[targetLabel]? = some (.original tl) ∧
      SelectedCopyRoute result label index ρ targetLabel ρ' ∧
      SourceDefinedAt f result.ctx tl 0 fr' ∧
      Inherited.CarryRel f result next.ctx next.block MR carried next.output.state (0,fr',cm) ρ' w := by
  have source := spec.split.block
  rw [spec.atBlock] at source
  obtain ⟨tl,middle,targetIndex,nonentry,successor,node⟩ :=
    stock_lower_selected_successor run scope tag source selected
  obtain ⟨targetBlock,args,regs,found,read,types,set,frame⟩ := enterBlock_spec entered
  have target : f.block? bc.block = some targetBlock := by rwa [before.1.1] at found
  have destination := blockIdx_block targetIndex target
  have nextAt : next.block = tl := by
    simpa only [sourceTargetIndex,targetIndex,Option.getD_some] using nextBlock
  have params : sourceTargetParams f bc = targetBlock.params.map (·.1) := by
    simp only [sourceTargetParams,target,Option.getD_some]
  have edge := edge_succ (mem_edgeIds_of_dests (List.mem_of_getElem? selected))
  have carriedAt : ∀ y,carried y → y ∈ availOf f (availIn f result.ctx) tl 0 := by
    intro y kept
    rw [← nextAt]
    exact carriedAvailable y kept
  have held := cover_held run scope spec.events spec.atBlock source destination edge targetIndex
    carriedAt (by rw [← nextAt,← params]; exact cover) before arguments
  obtain ⟨tl',targetLabel,ρ',targetIndex',targetTag,route,values⟩ :=
    stock_lower_selected_route_values run scope dominated tag source selected before.1.1 entered
      (needed := fun y => (Demanded next.output.state y ∧ y ∈ availOf f (availIn f result.ctx) tl 0) ∨
        carried y) (by
        intro y required
        have available : y ∈ availOf f (availIn f result.ctx) tl 0 := by
          rcases required with ⟨_,available⟩ | kept
          · exact available
          · exact carriedAt y kept
        simpa only [sourceTargetIndex,targetIndex,Option.getD_some] using available)
      (by rw [params]; exact held)
  have same : tl' = tl := Option.some.inj (targetIndex'.symm.trans targetIndex)
  subst tl'
  have dfg := stock_lower_source_enterBlock_dfg run scope dominated spec.events nextEvent
    source destination edge targetIndex before.1.1 (by simpa only [spec.atBlock] using before.1.2.1) entered
  have nextDefined := source_defined_enterBlock dominated.ssa result.ctx source before.1.1 edge
    targetIndex defined entered
  have convert : ∀ y key,result.ctx.valueReg? y = some (.vreg key .int) →
      next.ctx.valueReg? y = some (.vreg key .int) := by
    intro y key mapped
    rw [(stock_lower_record_context run scope nextEvent).2.1 y]
    exact mapped
  refine ⟨tl,targetLabel,ρ',targetIndex,targetTag,route,nextDefined,⟨?_,?_,?_,?_⟩,?_⟩
  · rw [frame]
    exact before.1.1
  · simpa only [nextAt] using dfg
  · simpa only [frame] using before.1.2.2.1
  · intro y required v get
    obtain ⟨key,mapped,value⟩ := values y (Or.inl ⟨required.1,by simpa only [nextAt] using required.2⟩) v get
    exact ⟨key,convert y key mapped,value⟩
  · intro y kept v get
    obtain ⟨key,mapped,value⟩ := values y (Or.inr kept) v get
    exact ⟨key,convert y key mapped,value⟩

end Backend.Stock.Proof.ConditionalValues

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem selected_successor_of {result : Result} {ps : Array (Array Nat)}
    (computed : result.code.cfg = .ok (result.order.successors,ps))
    {label index target : Nat} (selected : result.order.successors[label]![index]? = some target) :
    succOf result.code label index = some target := by
  cases row : result.order.successors[label]? with
  | none =>
    simp only [getElem!_def,row,Option.getD_none] at selected
    change (#[] : Array Nat)[index]? = some target at selected
    simp at selected
  | some values => simpa [succOf,computed,getElem!_def,row] using selected

/-- **`SelectedCopyRoute.execute` through the register update of the stop.** The selected actual
copy route runs from the register file that the stop instruction writes, as a terminator that
defines registers (the `jt_sequence`) does. -/
theorem SelectedCopyRoute.execute_update {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {isem : Backend.Proof.Sem} (driver : DriverSemG isem)
    {label index target k0 offset : Nat} {vb : VBlock} {code : List MInst}
    {ρ regs next : Nat → CV} {world prefixWorld endWorld : Arm.ArmState}
    {inst : MInst} {ops : Array Operand} {outs : List CV}
    (route : SelectedCopyRoute result label index (vdefUpd ops outs regs) target next)
    (block : result.code.blocks[label]? = some vb) (segment : SegAt vb k0 code)
    (execution : seqRun isem code ρ world =
      some (.stop offset inst ops regs prefixWorld outs endWorld (.goto index)))
    (last : k0+offset+1 = vb.insts.size) :
    Star (VStepAt result.code result.edgeArgs isem)
      (.run ⟨label,k0,ρ,world⟩) (.run ⟨target,0,next,endWorld⟩) := by
  obtain ⟨ps,computed⟩ := stock_lower_computed_cfg run scope
  cases route with
  | direct successor copied =>
    exact seqRun_goto_starAt (edges := result.edgeArgs) block segment execution last
      (selected_successor_of computed successor) copied
  | @synthetic middle successor identity successors placed copied =>
    have first := seqRun_goto_starAt (edges := result.edgeArgs) block segment execution last
      (selected_successor_of computed successor) identity
    obtain ⟨middleBlock,found,codeEq⟩ := placed
    have jumpRun : seqRun isem [.jump target] (vdefUpd ops outs regs) endWorld =
        some (.stop 0 (.jump target) #[] (vdefUpd ops outs regs) endWorld [] endWorld (.goto 0)) := by
      simp only [seqRun,show (MInst.jump target).operands = .ok #[] from rfl,
        show vuses (#[] : Array Operand) (vdefUpd ops outs regs) = [] from rfl,driver.jump]
      rfl
    have middleSegment : SegAt middleBlock 0 [.jump target] := by
      intro k bound
      have zero : k = 0 := by simp only [List.length_singleton] at bound; omega
      subst k
      rw [codeEq]
      rfl
    have lastMiddle : 0+0+1 = middleBlock.insts.size := by rw [codeEq]; rfl
    have nextSuccessor : result.order.successors[middle]![0]? = some target := by
      simp only [getElem!_def,successors,Option.getD_some]
      rfl
    have second := seqRun_goto_starAt found middleSegment jumpRun lastMiddle
      (selected_successor_of computed nextSuccessor)
      (by simpa only [vdefUpd,writeV,List.foldl_nil,Array.toList_empty,List.filter_nil,List.zip_nil_left,
        List.zip_nil_right] using copied)
    exact first.trans second

end Backend.Stock.Proof

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.TableBranch Backend.Stock.Proof.LoopCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem table_segment {f : Clif.Function} {result : Result} {b : Clif.Block} {label bi x : Nat}
    {dc : Clif.BlockCall} {tbl : List Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program} (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp) :
    SegAt {spec.raw with
      insts := spec.raw.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))
      params := spec.raw.params.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))
      branchArgs := spec.raw.branchArgs.map (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))}
      spec.preludeCode.size (spec.core.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) := by
  intro k hk
  have bound : k < spec.core.code.size := by simpa using hk
  simp only [spec.rawCode,Array.map_append]
  rw [Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
  simp only [Array.size_map,Nat.add_sub_cancel_left]
  simp [bound]

/-- `returning_selected_carry_below_of_labels` for a `br_table` from the conclusion of its carry
core: the selected successor may take arguments, through an original or a critical-edge
successor, and continues below the block's fuel from `CarryRel` of its own carry set. -/
theorem TableBodySpec.returning_selected_carry_below_of_core
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl)
    {carry : Nat → Prop} {vals : List Clif.Val} {cm : Clif.Mem} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state carry isem MR env cp vals cm fuel))
    {s : Clif.State} (callers : s.callers = [])
    {ρ : Nat → CV} {world : Arm.ArmState}
    (core : ReturningTableCarryCore spec carry fuel s vals cm ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) := by
  obtain ⟨t,left,fr,choice,bc,index,inst,ops,regs,prefixWorld,outs,endWorld,
    total,empty,frame,steps,selected,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ := core
  obtain ⟨next⟩ := successors choice bc selected
  have nextBlock : next.event.block = sourceTargetIndex f bc := by
    simpa only [sourceTargetIndex,next.lookup,Option.getD_some] using next.atBlock
  have arguments : ValuesHeld (fun y => y ∈ bc.args) result.ctx t.frame
      (fun key => vdefUpd ops outs regs (aliasNum result.final.alias key)) :=
    spec.selected_argument_values run scope dominated tag termShape post.1 selected
  have carriedAvailable : ∀ y,next.carried y →
      y ∈ availOf f (availIn f result.ctx) next.event.block 0 := by
    intro y kept
    rw [next.atBlock]
    exact next.available y kept
  have cover : EdgeCover f result next.event.block (sourceTargetParams f bc) next.event.output.state
      next.carried spec.term.output.state carry := by
    rw [next.atBlock]
    simp only [sourceTargetParams,next.found,Option.getD_some]
    exact next.cover
  obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
    spec.selected_successor_carry run scope dominated tag selected next.member nextBlock
      carriedAvailable cover post (by simpa only [spec.atBlock] using tDefined) crossed arguments
  have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
  subst tl
  have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
    (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
  subst targetLabel
  obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
  have destinationEq : destination = next.block := by
    rw [post.1.1] at found
    exact Option.some.inj (found.symm.trans next.found)
  have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
  have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
  have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
  have finished := next.returns left (by omega) {t with frame := fr} ρnext endWorld
    nextHeld.1.1 (frame.1.trans callers) bodyEq termEq nextDefined nextReturned nextHeld
  have endPosition : spec.preludeCode.size+(spec.body.code.size+index)+1 =
      (spec.raw.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias
        (result.final.alias.size+1)))).size := by
    simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append]
    omega
  have path := route.execute_update run scope driver.toDriverSemG spec.placed (table_segment spec) machine endPosition
  have whole := RunOkABIAt.prefix path finished
  simpa only [slotEq] using whole

/-- `trapping_selected_carry_below_of_labels` for a `br_table` from the conclusion of its carry
core. -/
theorem TableBodySpec.trapping_selected_carry_below_of_core
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl)
    {carry : Nat → Prop} {trapCode : Clif.TrapCode} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state carry isem MR env cp trapCode fuel))
    {s : Clif.State} (callers : s.callers = [])
    {ρ : Nat → CV} {world : Arm.ArmState}
    (core : TrappingTableCarryCore spec carry fuel s trapCode ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.trapped trapCode) := by
  rcases core with failed | ⟨t,left,fr,choice,bc,index,inst,ops,regs,prefixWorld,outs,endWorld,
    total,empty,frame,steps,selected,crossed,nextTrapped,tDefined,last,machine,post,targets,terminal⟩
  · obtain ⟨offset,i,ops,regs,prefixWorld,outs,endWorld,execution,coded⟩ := failed
    obtain ⟨path,bound,instruction,operands,semantics,arity,control⟩ :=
      seqRun_stop_starAt (edges := result.edgeArgs) spec.placed (table_segment spec) execution
    exact ⟨label,spec.preludeCode.size+offset,regs,prefixWorld,_,i,ops,outs,endWorld,path,
      spec.placed,instruction,operands,semantics,coded⟩
  · obtain ⟨next⟩ := successors choice bc selected
    have nextBlock : next.event.block = sourceTargetIndex f bc := by
      simpa only [sourceTargetIndex,next.lookup,Option.getD_some] using next.atBlock
    have arguments : ValuesHeld (fun y => y ∈ bc.args) result.ctx t.frame
        (fun key => vdefUpd ops outs regs (aliasNum result.final.alias key)) :=
      spec.selected_argument_values run scope dominated tag termShape post.1 selected
    have carriedAvailable : ∀ y,next.carried y →
        y ∈ availOf f (availIn f result.ctx) next.event.block 0 := by
      intro y kept
      rw [next.atBlock]
      exact next.available y kept
    have cover : EdgeCover f result next.event.block (sourceTargetParams f bc) next.event.output.state
        next.carried spec.term.output.state carry := by
      rw [next.atBlock]
      simp only [sourceTargetParams,next.found,Option.getD_some]
      exact next.cover
    obtain ⟨tl,targetLabel,ρnext,targetIndex,targetTag,route,nextDefined,nextHeld⟩ :=
      spec.selected_successor_carry run scope dominated tag selected next.member nextBlock
        carriedAvailable cover post (by simpa only [spec.atBlock] using tDefined) crossed arguments
    have indexEq : tl = next.index := Option.some.inj (targetIndex.symm.trans next.lookup)
    subst tl
    have labelEq : targetLabel = next.targetLabel := stock_blockOrder_original_unique
      (stock_lower_order run) (fun h => scope.nonempty (List.length_eq_zero_iff.mp h)) targetTag next.tag
    subst targetLabel
    obtain ⟨destination,args,sourceRegs,found,readArgs,types,set,frEq⟩ := enterBlock_spec crossed
    have destinationEq : destination = next.block := by
      rw [post.1.1] at found
      exact Option.some.inj (found.symm.trans next.found)
    have bodyEq : fr.body = next.block.body := by rw [frEq,destinationEq]
    have termEq : fr.term = next.block.term := by rw [frEq,destinationEq]
    have slotEq : fr.slots = s.frame.slots := by rw [frEq]; exact frame.2.2.1
    have finished := next.traps left (by omega) {t with frame := fr} ρnext endWorld
      nextHeld.1.1 (frame.1.trans callers) bodyEq termEq nextDefined nextTrapped nextHeld
    have endPosition : spec.preludeCode.size+(spec.body.code.size+index)+1 =
        (spec.raw.insts.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias
          (result.final.alias.size+1)))).size := by
      simp only [spec.rawCode,spec.bodyCode,Array.size_map,Array.size_append]
      omega
    have path := route.execute_update run scope driver.toDriverSemG spec.placed (table_segment spec) machine endPosition
    have whole := RunOkABIAt.prefix path finished
    simpa only [slotEq] using whole

/-- **A `br_table` on an `i32` index, with block arguments, composes below the fuel, for
returns.** The selected successor may take arguments, through an original or a critical-edge
successor. -/
theorem TableBodySpec.returning_selected_table_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : tbl.length < 4096)
    {carry : Nat → Prop}
    (available : ∀ y,carry y → y ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {vals : List Clif.Val} {cm : Clif.Mem} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state carry isem MR env cp vals cm fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) :=
  spec.returning_selected_carry_below_of_core run scope dominated driver tag termShape successors callers
    (spec.returning_table_carry_core run scope dominated family refines driver stable tag termShape typeX small
      available remaining atTerm defined returned held)

/-- **A `br_table` on an `i32` index, with block arguments, composes below the fuel, for first
traps.** -/
theorem TableBodySpec.trapping_selected_table_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : tbl.length < 4096)
    {carry : Nat → Prop}
    (available : ∀ y,carry y → y ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {trapCode : Clif.TrapCode} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state carry isem MR env cp trapCode fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped trapCode)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.trapped trapCode) :=
  spec.trapping_selected_carry_below_of_core run scope dominated driver tag termShape successors callers
    (spec.trapping_table_carry_core run scope dominated family refines driver stable tag termShape typeX small
      available remaining atTerm defined trapped held)

/-- **A `br_table` with empty block arguments composes below the fuel, for returns**: the
selected composition with arguments, as every argument list is empty. -/
theorem TableBodySpec.returning_empty_table_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : tbl.length < 4096) (_emptyArgs : ∀ bc ∈ dc :: tbl,bc.args = [])
    {carry : Nat → Prop}
    (available : ∀ y,carry y → y ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {vals : List Clif.Val} {cm : Clif.Mem} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryReturnBelow f result bc spec.term.output.state carry isem MR env cp vals cm fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.returned vals cm) :=
  spec.returning_selected_table_carry_below run scope dominated family refines driver stable tag termShape typeX
    small available successors callers remaining atTerm defined returned held

/-- **A `br_table` with empty block arguments composes below the fuel, for first traps.** -/
theorem TableBodySpec.trapping_empty_table_carry_below
    {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi x : Nat} {dc : Clif.BlockCall} {tbl : List Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : TableBodySpec f result b label bi x dc tbl isem MR env cp)
    (tag : result.order.nodes[label]? = some (.original bi))
    (termShape : b.term = .brTable x dc tbl) (typeX : result.ctx.valueType? x = some (.int 32))
    (small : tbl.length < 4096) (_emptyArgs : ∀ bc ∈ dc :: tbl,bc.args = [])
    {carry : Nat → Prop}
    (available : ∀ y,carry y → y ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {trapCode : Clif.TrapCode} {fuel : Nat}
    (successors : ∀ (index : Nat) (bc : Clif.BlockCall),(dests b.term)[index]? = some bc →
      Nonempty (SuccessorCarryTrapBelow f result bc spec.term.output.state carry isem MR env cp trapCode fuel))
    {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (trapped : Clif.runLoop env cp fuel s = .trapped trapCode)
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR carry
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,world⟩ (.trapped trapCode) :=
  spec.trapping_selected_table_carry_below run scope dominated family refines driver stable tag termShape typeX
    small available successors callers remaining atTerm defined trapped held

end Backend.Stock.Proof.ConditionalValues
