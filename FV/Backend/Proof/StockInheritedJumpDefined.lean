import FV.Backend.Proof.StockArithmeticTerminalDefined
import FV.Backend.Proof.StockInheritedBody
import FV.Backend.Proof.StockInheritedMixedDivision
import FV.Backend.Proof.StockJumpBodyRefines

namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem jump_seq {isem : Backend.Proof.Sem} (driver : DriverSem isem)
    (label : Nat) (ρ : Nat → CV) (w : Arm.ArmState) :
    seqRun isem [.jump label] ρ w = some (.stop 0 (.jump label) #[] ρ w [] w (.goto 0)) := by
  simp only [seqRun,show (MInst.jump label).operands = .ok #[] from rfl,
    show vuses (#[] : Array Operand) ρ = [] from rfl,driver.jump]
  rfl

/-- Finish the actual emitted jump after a proved source body execution.
This common continuation preserves source definedness and inherited source
values, independently of whether the whole source run later returns or traps. -/
theorem jump_continuation_defined {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    {isem : Backend.Proof.Sem} (driver : DriverSem isem) {MR : MemRelT}
    {env : Clif.Env} {cp : Clif.Program}
    (spec : Control.JumpBodySpec f result b label bi bc isem MR env cp)
    (jump : b.term = .jump bc) {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {s t : Clif.State}
    (steps : SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (List.range' (blockStart f spec.core.scan.block) b.body.length)
      (0,s.frame,s.mem) (b.body.length,t.frame,t.mem))
    (frame : LocalBody.SourceFrameEq s t) (atTerm : s.frame.term = b.term)
    {ρ ρ' : Nat → CV} {w w' : Arm.ArmState}
    (bodyRun : seqRun isem (spec.body.code.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w = some (.fall ρ' w'))
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame) :
    (∀ x,needed x → t.frame.regs x = s.frame.regs x) ∧ t.frame.term = .jump bc ∧
      seqRun isem (spec.core.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ' w' [] w' (.goto 0)) ∧
      SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame := by
  have tDefined : SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame := by
    apply ArithmeticBody.arithmetic_steps_defined run scope dominated spec.events spec.split.block
      (env := env) (cp := cp) (s := (0,s.frame,s.mem)) (t := (b.body.length,t.frame,t.mem))
      (j := 0) (n := b.body.length) (by omega) rfl ?_ defined
    simpa only [Nat.add_zero,Nat.sub_zero] using steps
  have positions : ∀ i ∈ List.range' (blockStart f spec.core.scan.block) b.body.length,
      ∃ j stm,b.body[j]? = some stm ∧ i = blockStart f spec.core.scan.block+j := by
    intro i member
    rw [List.range'_eq_map_range] at member
    obtain ⟨j,inside,rfl⟩ := List.mem_map.mp member
    have bound := List.mem_range.mp inside
    exact ⟨j,b.body[j],List.getElem?_eq_getElem bound,rfl⟩
  have sourceFrame := source_steps_entry_carry run spec.events spec.split available positions steps
  refine ⟨sourceFrame,frame.2.2.2.trans (atTerm.trans jump),?_,tDefined⟩
  have code : spec.core.code.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      spec.body.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ [.jump spec.target] := by
    rw [spec.bodyCode,Array.toList_append,List.map_append]
    rfl
  rw [code]
  have executed := seqRun_append_fall_stop isem bodyRun (jump_seq driver spec.target ρ' w')
  simpa only [List.length_map,Array.length_toList,Nat.zero_add] using executed

private theorem local_jump_carry_returns_defined {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : Control.JumpBodySpec f result b label bi bc isem MR env cp)
    (jump : b.term = .jump bc)
    (localFamily : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    (bodyRefines : ∀ a a',SourceSteps (IndexedSourceInst env cp f spec.core.scan.ctx spec.core.scan.block)
      (sourceBodyIndices f spec.core.scan.block b).reverse a a' → ∀ ρ w,
      CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.body.state a ρ w → ∃ ρ' w',
        seqRun isem (spec.body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧ CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed
              spec.term.output.state a' ρ' w')
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm) {ρ : Nat → CV} {w : Arm.ArmState}
    (held : CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame) :
    ∃ t left ρ' w',left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .returned vals cm ∧
      t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
      (∀ x,needed x → t.frame.regs x = s.frame.regs x) ∧ t.frame.term = .jump bc ∧
      seqRun isem (spec.core.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ' w' [] w' (.goto 0)) ∧
      CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
        (b.body.length,t.frame,t.mem) ρ' w' ∧
      SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame := by
  obtain ⟨t,left,total,continued,empty,steps,frame⟩ := LocalBody.actual_local_source_execution_frame
    run spec.events spec.split localFamily (j := 0) (by omega) (by simpa using remaining) returned
  obtain ⟨ρ',w',bodyRun,post⟩ := bodyRefines (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse] using steps)
    ρ w (by simpa only [spec.split.state] using held)
  obtain ⟨sourceFrame,atJump,executed,tDefined⟩ := jump_continuation_defined run scope dominated driver spec jump
    available (by simpa only [Nat.add_zero,Nat.sub_zero] using steps) frame atTerm bodyRun defined
  exact ⟨t,left,ρ',w',by simpa using total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined⟩

/-- Definedness-retaining variant: a complete actual constant/nop body and its emitted jump preserve the
inherited-value invariant, with the original source continuation and fuel.
The carried values need not be demanded at this compiler scan position. -/
theorem constant_jump_carry_returns_defined {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : Control.JumpBodySpec f result b label bi bc isem MR env cp)
    (jump : b.term = .jump bc)
    (family : ∀ stm ∈ b.body,(∃ ty imm,stm.inst = .iconst ty imm) ∨ stm.inst = .nop)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm) {ρ : Nat → CV} {w : Arm.ArmState}
    (held : CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame) :
    ∃ t left ρ' w',left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .returned vals cm ∧
      t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
      (∀ x,needed x → t.frame.regs x = s.frame.regs x) ∧ t.frame.term = .jump bc ∧
      seqRun isem (spec.core.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ' w' [] w' (.goto 0)) ∧
      CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
        (b.body.length,t.frame,t.mem) ρ' w' ∧
      SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame := by
  have localFamily : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
    intro stm member
    rcases family stm member with ⟨ty,imm,shape⟩ | shape
    · rw [shape]
      exact LocalBody.LocalInst.of_pure rfl
    · rw [shape]
      exact True.intro
  exact local_jump_carry_returns_defined run scope dominated refines driver stable spec jump localFamily available
    (constant_body_carry_fall_refines run scope dominated spec.events spec.split family available refines driver stable)
    remaining atTerm returned held defined

/-- Actual entry divisions and constant/nop records preserve inherited values
through the same emitted jump on normal source return. Source formats may
come from broader families in other blocks; no code or value certificate is
added. The first local trap is handled separately from successor continuation. -/
theorem division_jump_carry_returns_defined {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} {label bi : Nat} {bc : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : Control.JumpBodySpec f result b label bi bc isem MR env cp)
    (jump : b.term = .jump bc)
    (formats : ∀ block ∈ f.blocks,∀ stm ∈ block.body,CastComplete.MemoryFormat stm.inst)
    (family : ∀ stm ∈ b.body,(∃ ty imm,stm.inst = .iconst ty imm) ∨
      (∃ op ty x y,stm.inst = .div op ty x y) ∨ stm.inst = .nop)
    {needed : Nat → Prop}
    (available : ∀ x,needed x → x ∈ availOf f (availIn f result.ctx) spec.core.scan.block 0)
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm) {ρ : Nat → CV} {w : Arm.ArmState}
    (held : CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame) :
    ∃ t left ρ' w',left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .returned vals cm ∧
      t.frame.body = [] ∧ LocalBody.SourceFrameEq s t ∧
      (∀ x,needed x → t.frame.regs x = s.frame.regs x) ∧ t.frame.term = .jump bc ∧
      seqRun isem (spec.core.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
          some (.stop spec.body.code.size (.jump spec.target) #[] ρ' w' [] w' (.goto 0)) ∧
      CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.term.output.state
        (b.body.length,t.frame,t.mem) ρ' w' ∧
      SourceDefinedAt f result.ctx spec.core.scan.block b.body.length t.frame := by
  have localFamily : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
    intro stm member
    rcases family stm member with ⟨ty,imm,shape⟩ | ⟨op,ty,x,y,shape⟩ | shape
    · rw [shape]
      exact LocalBody.LocalInst.of_pure rfl
    · rw [shape]
      exact True.intro
    · rw [shape]
      exact True.intro
  exact local_jump_carry_returns_defined run scope dominated refines driver stable spec jump localFamily available
    (constant_division_body_carry_refines_local run scope dominated spec.events spec.split formats family
      available refines driver stable).1 remaining atTerm returned held defined

end Backend.Stock.Proof.Inherited
