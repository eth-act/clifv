import FV.Backend.Proof.StockLoopCarry
import FV.Backend.Proof.StockComparisonSourceCores
import FV.Backend.Proof.StockComparisonImmCores
import FV.Backend.Proof.StockComparisonZeroCores

/-! Comparison branches with carry sets (#140, T7b-7).

`returning/trapping_parameter_carry_core` add a carry set to the parameter-branch cores: the body
keeps `CarryRel` (`scalar_body_carry_refines`), and the branch defines no virtual registers. The
comparison branches also define no virtual registers: `subs` and `b.cond` for two parameters or
for a 12-bit immediate, `cbz`/`cbnz` for zero (`Calls.comparison_wide_no_defs`,
`Calls.comparison_imm_no_defs`, `Calls.comparison_zero_no_defs`). So the same argument
(`branch_carry_of_no_defs`) gives the carry cores of the three comparison forms.
`ComparisonMetadata` collects the context metadata of the three forms, and
`returning/trapping_comparison_any_carry_core` dispatch on it. -/

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LoopCarry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The conclusion of `returning_parameter_carry_core`: the source runs the body and the branch,
then returns from the selected successor with `left` fuel; the actual core code stops at the
branch's last instruction, and the block's end holds `CarryRel` of `needed`. -/
def ReturningCarryCore {f : Clif.Function} {result : Result} {b : Clif.Block} {label bi c : Nat}
    {yes no : Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (needed : Nat → Prop) (fuel : Nat) (s : Clif.State) (vals : List Clif.Val) (cm : Clif.Mem)
    (ρ : Nat → CV) (world : Arm.ArmState) : Prop :=
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
    Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
      (b.body.length,t.frame,t.mem) regs endWorld ∧
    inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true

/-- The conclusion of `trapping_parameter_carry_core`: the actual core code traps in the body,
or `ReturningCarryCore` with a later source trap in place of the return. -/
def TrappingCarryCore {f : Clif.Function} {result : Result} {b : Clif.Block} {label bi c : Nat}
    {yes no : Clif.BlockCall} {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env}
    {cp : Clif.Program} (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (needed : Nat → Prop) (fuel : Nat) (s : Clif.State) (code : Clif.TrapCode)
    (ρ : Nat → CV) (world : Arm.ArmState) : Prop :=
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
    Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
      (b.body.length,t.frame,t.mem) regs endWorld ∧
    inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true

/-- The body keeps every carried value (`scalar_body_carry_refines`), and a branch emission that
defines no virtual registers keeps the registers of the body's end. This is `branch_carry` of
`StockLoopCarry` with the no-definition fact as a premise. -/
theorem ConditionalBodySpec.branch_carry_of_no_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (noDefs : ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [])
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {s t : Clif.State}
    (steps : SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (List.range' (blockStart f spec.core.scan.block) b.body.length)
      (0,s.frame,s.mem) (b.body.length,t.frame,t.mem))
    {ρ : Nat → CV} {world : Arm.ArmState}
    (held : Inherited.CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
      spec.core.scan.output.state (0,s.frame,s.mem) ρ world)
    {index : Nat} {inst : MInst} {ops : Array Operand} {regs : Nat → CV} {prefixWorld : Arm.ArmState}
    {outs : List CV} {endWorld : Arm.ArmState} {control : Ctl}
    (machine : seqRun isem (spec.core.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
      some (.stop index inst ops regs prefixWorld outs endWorld control)) :
    ValuesHeld needed spec.core.scan.ctx t.frame (fun key => regs (aliasNum result.final.alias key)) := by
  have block := spec.split.block
  have formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    exact MaskBody.family_formats (family block member stm present)
  obtain ⟨ρ',w',bodyRun,post⟩ := (Inherited.scalar_body_carry_refines run scope dominated spec.events spec.split
    formats (family b (List.mem_of_getElem? block)) available refines driver stable (env := env) (cp := cp)).1
    (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse] using steps)
    ρ world (by simpa only [spec.split.state] using held)
  rw [spec.bodyCode,Array.toList_append,List.map_append,seqRun_append_fall isem bodyRun] at machine
  cases branch : seqRun isem (spec.origin.emission.code.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ' w' with
  | none =>
    rw [branch] at machine
    cases machine
  | some ending =>
    rw [branch] at machine
    cases ending with
    | fall _ _ => cases machine
    | stop index' inst' ops' regs' prefixWorld' outs' endWorld' control' =>
      simp only [Option.map_some,Option.some.injEq,SeqEnd.shift,SeqEnd.stop.injEq] at machine
      obtain ⟨_,_,_,registers,_⟩ := machine
      subst registers
      have frame : ∀ key,regs' key = ρ' key := by
        intro key
        apply Sequence.stop_frame isem branch key
        intro selected member defined
        obtain ⟨raw,inside,rfl⟩ := List.mem_map.mp member
        rw [Resolved.renamed_defs,noDefs raw inside,List.map_nil] at defined
        exact List.not_mem_nil defined
      have registerEq : regs' = ρ' := funext frame
      rw [registerEq]
      exact post.2

/-- The actual branch on a direct wide comparison of two source parameters defines no virtual
registers. -/
theorem ConditionalBodySpec.comparison_branch_no_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : result.ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none) (parameterY : result.ctx.defInst? y = none) :
    ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have typeXHere : spec.core.scan.ctx.valueType? x = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeX
  have typeYHere : spec.core.scan.ctx.valueType? y = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeY
  have parameterXHere : spec.core.scan.ctx.defInst? x = none := by rw [ctxEq]; exact parameterX
  have parameterYHere : spec.core.scan.ctx.defInst? y = none := by rw [ctxEq]; exact parameterY
  obtain ⟨calls,source⟩ := spec.comparison_calls run scope block termShape origin parameterX
  obtain ⟨code,fragment,noDefs⟩ :=
    calls.comparison_wide_no_defs inv source originHere wide typeXHere typeYHere parameterXHere parameterYHere
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  rw [actualCode]
  exact noDefs

/-- The actual branch on a direct wide comparison of a source parameter with an encodable
constant defines no virtual registers. -/
theorem ConditionalBodySpec.comparison_imm_branch_no_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0) :
    ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have constYHere := spec.defClif_here block constY
  have typeXHere : spec.core.scan.ctx.valueType? x = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeX
  have parameterXHere : spec.core.scan.ctx.defInst? x = none := by rw [ctxEq]; exact parameterX
  obtain ⟨calls,source⟩ := spec.comparison_calls run scope block termShape origin parameterX
  obtain ⟨code,fragment,noDefs⟩ :=
    calls.comparison_imm_no_defs inv source originHere wide typeXHere parameterXHere constYHere fits nonzero
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  rw [actualCode]
  exact noDefs

/-- The actual `cbz`/`cbnz` branch on a direct wide `eq`/`ne` comparison of a source parameter
with zero defines no virtual registers. -/
theorem ConditionalBodySpec.comparison_zero_branch_no_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {isem : Backend.Proof.Sem} {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0) :
    ∀ m ∈ spec.origin.emission.code.toList,vdefs m = [] := by
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have originHere := spec.defClif_here block origin
  have constYHere := spec.defClif_here block constY
  have typeXHere : spec.core.scan.ctx.valueType? x = some (.int (if wide then 64 else 32)) := by
    rw [ctxEq]; exact typeX
  have parameterXHere : spec.core.scan.ctx.defInst? x = none := by rw [ctxEq]; exact parameterX
  obtain ⟨calls,source⟩ := spec.comparison_calls run scope block termShape origin parameterX
  obtain ⟨code,fragment,noDefs⟩ :=
    calls.comparison_zero_no_defs inv source originHere wide typeXHere parameterXHere constYHere equality zero
  have actualCode : spec.origin.emission.code.toList = code := by
    rw [spec.origin.emitted]
    have buffers := congrArg Array.toList fragment.emitted
    simpa only [Array.toList_append,Array.toList_empty,List.toList_toArray,List.nil_append] using buffers
  rw [actualCode]
  exact noDefs

/-- `returning_comparison_core` with a carry set: the body and the comparison branch keep
`CarryRel` of every set that is available at the block entry. -/
theorem ConditionalBodySpec.returning_comparison_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : result.ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none) (parameterY : result.ctx.defInst? y = none)
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
  have noDefs := spec.comparison_branch_no_defs run scope block termShape origin wide typeX typeY
    parameterX parameterY
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_comparison_core run scope dominated family refines driver stable termShape origin wide
      typeX typeY parameterX parameterY remaining atTerm defined returned held.1
  exact ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,crossed,
    nextReturned,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family refines
      driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- `trapping_comparison_core` with a carry set. -/
theorem ConditionalBodySpec.trapping_comparison_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (typeY : result.ctx.valueType? y = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none) (parameterY : result.ctx.defInst? y = none)
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
  have noDefs := spec.comparison_branch_no_defs run scope block termShape origin wide typeX typeY
    parameterX parameterY
  rcases spec.trapping_comparison_core run scope dominated family refines driver stable termShape origin wide
      typeX typeY parameterX parameterY remaining atTerm defined trapped held.1 with
    failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
      total,empty,frame,steps,read,crossed,nextTrapped,tDefined,last,machine,post,targets,terminal⟩
  · exact Or.inl failed
  · exact Or.inr ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,
      crossed,nextTrapped,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family
        refines driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- `returning_comparison_imm_core` with a carry set. -/
theorem ConditionalBodySpec.returning_comparison_imm_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0)
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
  have noDefs := spec.comparison_imm_branch_no_defs run scope block termShape origin wide typeX parameterX
    constY fits nonzero
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_comparison_imm_core run scope dominated family refines driver stable termShape origin wide
      typeX parameterX constY fits nonzero remaining atTerm defined returned held.1
  exact ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,crossed,
    nextReturned,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family refines
      driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- `trapping_comparison_imm_core` with a carry set. -/
theorem ConditionalBodySpec.trapping_comparison_imm_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    {imm : Imm12} (fits : Imm12.ofNat? k.toNat = some imm)
    (nonzero : cc = .eq ∨ cc = .ne → k ≠ 0)
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
  have noDefs := spec.comparison_imm_branch_no_defs run scope block termShape origin wide typeX parameterX
    constY fits nonzero
  rcases spec.trapping_comparison_imm_core run scope dominated family refines driver stable termShape origin
      wide typeX parameterX constY fits nonzero remaining atTerm defined trapped held.1 with
    failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
      total,empty,frame,steps,read,crossed,nextTrapped,tDefined,last,machine,post,targets,terminal⟩
  · exact Or.inl failed
  · exact Or.inr ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,
      crossed,nextTrapped,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family
        refines driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- `returning_comparison_zero_core` with a carry set. -/
theorem ConditionalBodySpec.returning_comparison_zero_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0)
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
  have noDefs := spec.comparison_zero_branch_no_defs run scope block termShape origin wide typeX parameterX
    constY equality zero
  obtain ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
    total,empty,frame,steps,read,crossed,nextReturned,tDefined,last,machine,post,targets,terminal⟩ :=
    spec.returning_comparison_zero_core run scope dominated family refines driver stable termShape origin wide
      typeX parameterX constY equality zero remaining atTerm defined returned held.1
  exact ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,crossed,
    nextReturned,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family refines
      driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- `trapping_comparison_zero_core` with a carry set. -/
theorem ConditionalBodySpec.trapping_comparison_zero_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no)
    {cc : Clif.IntCC} {ty : Clif.Ty} {x y : Nat}
    (origin : result.ctx.defClif? c = some (.icmp cc ty x y)) (wide : Bool)
    (typeX : result.ctx.valueType? x = some (.int (if wide then 64 else 32)))
    (parameterX : result.ctx.defInst? x = none)
    {ty' : Clif.Ty} {k : BitVec ty'.width} (constY : result.ctx.defClif? y = some (.iconst ty' k))
    (equality : cc = .eq ∨ cc = .ne) (zero : k = 0)
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
  have noDefs := spec.comparison_zero_branch_no_defs run scope block termShape origin wide typeX parameterX
    constY equality zero
  rcases spec.trapping_comparison_zero_core run scope dominated family refines driver stable termShape origin
      wide typeX parameterX constY equality zero remaining atTerm defined trapped held.1 with
    failed | ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,
      total,empty,frame,steps,read,crossed,nextTrapped,tDefined,last,machine,post,targets,terminal⟩
  · exact Or.inl failed
  · exact Or.inr ⟨t,left,value,fr,index,inst,ops,regs,prefixWorld,endWorld,total,empty,frame,steps,read,
      crossed,nextTrapped,tDefined,last,machine,⟨post,spec.branch_carry_of_no_defs run scope dominated family
        refines driver stable noDefs available steps held machine⟩,targets,terminal⟩

/-- Context metadata of a branch condition `c` in one of the three forms of the comparison
cores: `icmp` of two wide parameters of one width; `icmp` of a wide parameter with an encodable
12-bit `iconst`, nonzero for `eq`/`ne`; or `icmp eq`/`ne` of a wide parameter with `iconst 0`. -/
def ComparisonMetadata (ctx : Ctx) (c : Nat) : Prop :=
  (∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool),
    ctx.defClif? c = some (.icmp cc ty x y) ∧
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧
    ctx.valueType? y = some (.int (if wide then 64 else 32)) ∧
    ctx.defInst? x = none ∧ ctx.defInst? y = none) ∨
  (∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool) (ty' : Clif.Ty) (k : BitVec ty'.width)
      (imm : Imm12),
    ctx.defClif? c = some (.icmp cc ty x y) ∧
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧ ctx.defInst? x = none ∧
    ctx.defClif? y = some (.iconst ty' k) ∧ Imm12.ofNat? k.toNat = some imm ∧
    (cc = .eq ∨ cc = .ne → k ≠ 0)) ∨
  (∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat) (wide : Bool) (ty' : Clif.Ty) (k : BitVec ty'.width),
    ctx.defClif? c = some (.icmp cc ty x y) ∧
    ctx.valueType? x = some (.int (if wide then 64 else 32)) ∧ ctx.defInst? x = none ∧
    ctx.defClif? y = some (.iconst ty' k) ∧ (cc = .eq ∨ cc = .ne) ∧ k = 0)

/-- Every comparison form is an `icmp` whose first operand is a parameter. -/
theorem ComparisonMetadata.origin {ctx : Ctx} {c : Nat} (comparison : ComparisonMetadata ctx c) :
    ∃ (cc : Clif.IntCC) (ty : Clif.Ty) (x y : Nat),
      ctx.defClif? c = some (.icmp cc ty x y) ∧ ctx.defInst? x = none := by
  rcases comparison with ⟨cc,ty,x,y,_,origin,_,_,parameterX,_⟩ |
    ⟨cc,ty,x,y,_,_,_,_,origin,_,parameterX,_⟩ | ⟨cc,ty,x,y,_,_,_,origin,_,parameterX,_⟩
  · exact ⟨cc,ty,x,y,origin,parameterX⟩
  · exact ⟨cc,ty,x,y,origin,parameterX⟩
  · exact ⟨cc,ty,x,y,origin,parameterX⟩

/-- The carry return core of a branch on a comparison in any of the three forms. -/
theorem ConditionalBodySpec.returning_comparison_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComparisonMetadata result.ctx c)
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
  rcases comparison with ⟨cc,ty,x,y,wide,origin,typeX,typeY,parameterX,parameterY⟩ |
    ⟨cc,ty,x,y,wide,ty',k,imm,origin,typeX,parameterX,constY,fits,nonzero⟩ |
    ⟨cc,ty,x,y,wide,ty',k,origin,typeX,parameterX,constY,equality,zero⟩
  · exact spec.returning_comparison_carry_core run scope dominated family refines driver stable termShape
      origin wide typeX typeY parameterX parameterY available remaining atTerm defined returned held
  · exact spec.returning_comparison_imm_carry_core run scope dominated family refines driver stable termShape
      origin wide typeX parameterX constY fits nonzero available remaining atTerm defined returned held
  · exact spec.returning_comparison_zero_carry_core run scope dominated family refines driver stable termShape
      origin wide typeX parameterX constY equality zero available remaining atTerm defined returned held

/-- The carry first-trap core of a branch on a comparison in any of the three forms. -/
theorem ConditionalBodySpec.trapping_comparison_any_carry_core {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (termShape : b.term = .brif c yes no) (comparison : ComparisonMetadata result.ctx c)
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
  rcases comparison with ⟨cc,ty,x,y,wide,origin,typeX,typeY,parameterX,parameterY⟩ |
    ⟨cc,ty,x,y,wide,ty',k,imm,origin,typeX,parameterX,constY,fits,nonzero⟩ |
    ⟨cc,ty,x,y,wide,ty',k,origin,typeX,parameterX,constY,equality,zero⟩
  · exact spec.trapping_comparison_carry_core run scope dominated family refines driver stable termShape
      origin wide typeX typeY parameterX parameterY available remaining atTerm defined trapped held
  · exact spec.trapping_comparison_imm_carry_core run scope dominated family refines driver stable termShape
      origin wide typeX parameterX constY fits nonzero available remaining atTerm defined trapped held
  · exact spec.trapping_comparison_zero_carry_core run scope dominated family refines driver stable termShape
      origin wide typeX parameterX constY equality zero available remaining atTerm defined trapped held

end Backend.Stock.Proof.ConditionalValues
