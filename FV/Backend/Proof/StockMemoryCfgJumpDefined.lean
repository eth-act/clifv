import FV.Backend.Proof.StockInheritedJumpDefined

/-! UNVALIDATED next-batch source. The frozen production packet excludes this file.
Reuse the existing local jump composition without excluding memory instructions
in other blocks. The caller must derive the entry body proof from actual records.
Keep every existing public and private variant unchanged. -/
namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Compose a proved local body and the actual jump while preserving source definedness. -/
theorem local_jump_carry_returns_defined_of_body {f : Clif.Function} {result : Result}
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


end Backend.Stock.Proof.Inherited
