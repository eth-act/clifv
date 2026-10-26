import FV.Backend.Proof.StockLocalSourceContinuation
import FV.Backend.Proof.StockArithmeticTerminalDefined
import FV.Backend.Proof.StockInheritedBody
import FV.Backend.Proof.StockInheritedJumpDefined
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

private theorem quiet_no_source_traps {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body,(∃ ty imm,stm.inst = .iconst ty imm) ∨ stm.inst = .nop)
    {env : Clif.Env} {cp : Clif.Program} {indices : List Nat}
    (positions : ∀ i ∈ indices,∃ j stm,b.body[j]? = some stm ∧ i = blockStart f event.block+j)
    {s : SourcePoint} {code : Clif.TrapCode}
    (failed : SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block) indices s code) : False := by
  induction failed with
  | @here i rest s code failed =>
    obtain ⟨j,stm,statement,current⟩ := positions i (List.mem_cons_self ..)
    obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split
      (record := ⟨i,default,default⟩) statement current
    obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
    cases Option.some.inj (found.symm.trans source)
    cases Option.some.inj (original.symm.trans clif)
    rcases family stm (List.mem_of_getElem? statement) with ⟨ty,imm,shape⟩ | shape
    · rw [shape,LocalBody.local_outcome (show LocalBody.LocalInst (.iconst ty imm) from rfl)] at trapped
      simp [Clif.evalInst] at trapped
    · rw [shape,LocalBody.local_outcome (show LocalBody.LocalInst .nop from True.intro)] at trapped
      cases trapped
  | next head tail ih =>
    exact ih (fun i member => positions i (List.mem_cons_of_mem _ member))

/-- Definedness-retaining variant: a complete actual constant/nop body and its emitted jump preserve the
inherited-value invariant, with the original source continuation and fuel.
The carried values need not be demanded at this compiler scan position. -/
theorem constant_jump_carry_traps_defined {f : Clif.Function} {result : Result}
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
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (trapped : Clif.runLoop env cp fuel s = .trapped code) {ρ : Nat → CV} {w : Arm.ArmState}
    (held : CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame) :
    ∃ t left ρ' w',left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .trapped code ∧
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
  have sourcePositions : ∀ i ∈ List.range' (blockStart f spec.core.scan.block) b.body.length,
      ∃ j stm,b.body[j]? = some stm ∧ i = blockStart f spec.core.scan.block+j := by
    intro i member
    rw [List.range'_eq_map_range] at member
    obtain ⟨j,inside,rfl⟩ := List.mem_map.mp member
    have bound := List.mem_range.mp inside
    exact ⟨j,b.body[j],List.getElem?_eq_getElem bound,rfl⟩
  have continuation := LocalBody.actual_local_source_trap_or_continue run spec.events spec.split
    localFamily (j := 0) (by omega) (by simpa using remaining) trapped
  have cannotTrap := quiet_no_source_traps run spec.events spec.split family sourcePositions
    (env := env) (cp := cp) (s := (0,s.frame,s.mem)) (code := code)
  obtain ⟨t,left,total,continued,empty,steps,frame⟩ := continuation.resolve_left
    (by simpa only [Nat.add_zero,Nat.sub_zero] using cannotTrap)
  obtain ⟨ρ',w',bodyRun,post⟩ := constant_body_carry_fall_refines run scope dominated spec.events spec.split
    family available refines driver stable (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse] using steps)
    ρ w (by simpa only [spec.split.state] using held)
  obtain ⟨sourceFrame,atJump,executed,tDefined⟩ := jump_continuation_defined run scope dominated driver spec jump
    available (by simpa only [Nat.add_zero,Nat.sub_zero] using steps) frame atTerm bodyRun defined
  exact ⟨t,left,ρ',w',by simpa using total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined⟩

/-- A genuine first trap in the entry body stops before its jump. Otherwise,
the complete body/jump carries inherited values to the later source trap.
The two outcomes retain their original source continuation and fuel. -/
theorem division_jump_carry_traps_or_continues_defined {f : Clif.Function} {result : Result}
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
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (trapped : Clif.runLoop env cp fuel s = .trapped code) {ρ : Nat → CV} {w : Arm.ArmState}
    (held : CarryRel f result spec.core.scan.ctx spec.core.scan.block MR needed spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame) :
    TrapRun isem (spec.core.code.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code ∨
    ∃ t left ρ' w',left+b.body.length = fuel ∧ Clif.runLoop env cp left t = .trapped code ∧
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
  have bodies := constant_division_body_carry_refines_local run scope dominated spec.events spec.split
    formats family available refines driver stable (env := env) (cp := cp)
  rcases LocalBody.actual_local_source_trap_or_continue run spec.events spec.split
    localFamily (j := 0) (by omega) (by simpa using remaining) trapped with
    failed | ⟨t,left,total,continued,empty,steps,frame⟩
  · left
    have failedRun := bodies.2 (0,s.frame,s.mem) code
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse] using failed)
      ρ w (by simpa only [spec.split.state] using held)
    rw [spec.bodyCode,Array.toList_append,List.map_append]
    exact failedRun.append
  · right
    obtain ⟨ρ',w',bodyRun,post⟩ := bodies.1 (0,s.frame,s.mem) (b.body.length,t.frame,t.mem)
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range,sourceBodyIndices,List.reverse_reverse] using steps)
      ρ w (by simpa only [spec.split.state] using held)
    obtain ⟨sourceFrame,atJump,executed,tDefined⟩ := jump_continuation_defined run scope dominated driver spec jump
      available (by simpa only [Nat.add_zero,Nat.sub_zero] using steps) frame atTerm bodyRun defined
    exact ⟨t,left,ρ',w',by simpa using total,continued,empty,frame,sourceFrame,atJump,executed,post,tDefined⟩

end Backend.Stock.Proof.Inherited
