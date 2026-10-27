import FV.Backend.Proof.StockInheritedMixedDivision
import FV.Backend.Proof.StockDivUdivWideWitness
import FV.Backend.Proof.StockEntrySeed
import FV.Backend.Proof.LowerShapeOkFacts
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.InheritedDivisionWitness
open Backend.Proof Backend.Proof.Driver
open ScalarDiv.UdivWideWitness.RunData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private def initial (denominator : BitVec 64) : Clif.Frame := {
  func := function
  regs := (Clif.Regs.empty.set 7 ⟨.i64,7⟩).set 31 ⟨.i64,denominator⟩
  slots := []
  body := function.blocks[0]!.body
  term := function.blocks[0]!.term }

private def after : Clif.Frame := {initial 3 with
  regs := (initial 3).regs.set 100 ⟨.i64,2⟩
  body := []}

private structure Inputs where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  term : ScanRecord
  body : BlockScan
  step : Step
  info : IInfo
  run : Stock.lower function = .ok result
  scope : LowerScope function
  dominated : Dominated function
  events : event ∈ result.blockScans.toList
  atBlock : event.block = 0
  records : record ∈ event.output.records
  split : SourceBodySplit function event function.blocks[0]! term body
  current : record.inst = 0
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.div .udiv .i64 7 31)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted

private theorem inputs : Nonempty Inputs := by
  obtain ⟨result,oldEvent,oldRecord,oldStep,d,fr',run,scope,dominated,rest⟩ :=
    ScalarDiv.UdivWideWitness.stock_udiv_wide_success_witness
  have actual := observed
  rw [run] at actual
  simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
    decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
  obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,stepData⟩ := actual
  simp only [ctxKey,Prod.mk.injEq] at ctxEq
  obtain ⟨insts,types,defs,maps⟩ := ctxEq
  obtain ⟨step,recorded,emitted,selected⟩ := (by
    simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
      ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
        step.rules.getLast? = some Isle.Aarch64.rule_lower_1116.id)
  have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
      some (some (.div .udiv .i64 7 31),[100]) := by
    rw [← Array.getElem?_map,insts,current]
    decide +kernel
  obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
  have clif := congrArg Prod.fst keyEq
  have results := congrArg Prod.snd keyEq
  obtain ⟨b,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have atBlock : event.block = 0 := by
    have bound := (List.getElem?_eq_some_iff.mp split.block).1
    change event.block < 1 at bound
    omega
  have same : b = function.blocks[0]! := Option.some.inj (split.block.symm.trans (by rw [atBlock]; rfl))
  subst b
  have mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int) := by
    simpa only [Ctx.valueReg?,maps] using (show built.1.valueReg? 100 = some (.vreg 194 .int) from rfl)
  exact ⟨⟨result,event,record,term,body,step,info,run,scope,dominated,events,atBlock,records,
    split,current,source,clif,results,mapped,recorded,emitted⟩⟩

private theorem carry_available (input : Inputs) :
    ∀ x,x = 7 → x ∈ availOf function (availIn function input.result.ctx) input.event.block 0 := by
  intro x equal
  subst x
  rw [input.atBlock]
  have block : function.blocks[0]? = some function.blocks[0]! := rfl
  apply (mem_av block).mpr
  refine ⟨Or.inl (by decide +kernel),?_⟩
  rintro ⟨j,stm,_,found,defined⟩
  exact param_not_result input.dominated.ssa (List.mem_of_getElem? block) (List.mem_of_getElem? block)
    (by decide +kernel) (List.mem_flatMap.mpr ⟨stm,List.mem_of_getElem? found,defined⟩)

private theorem entry_carry (input : Inputs) (denominator : BitVec 64) (world : Arm.ArmState) :
    Inherited.CarryRel function input.result input.event.ctx input.event.block (fun _ _ _ => True)
      (fun x => x = 7) input.record.output.state (0,initial denominator,Clif.Mem.empty)
      (entrySeed input.event.ctx (initial denominator)) world := by
  have entered : Clif.enterFunc function [⟨.i64,7⟩,⟨.i64,denominator⟩] Clif.Mem.empty =
      .ok (initial denominator,Clif.Mem.empty) := rfl
  exact ⟨stock_lower_entered_seed_guarded input.run input.scope input.dominated input.events entered
      input.record.output.state world True.intro,
    (entrySeed_entered_resolved_values_frame input.run input.scope input.dominated input.events
      (SourceEntry.of_enterFunc entered)).mono (fun _ _ => True.intro)⟩

/-- A real original7/3 source step produces2 while the extended invariant
retains the defined entry7. Compilation, source entry and the seed guard are
derived from existing complete witnesses, with no new finite check or axiom. -/
theorem executable_division_carry_witness (X : ExtSem) :
    ∃ result event record term body ρ w key,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      SourceBodySplit function event function.blocks[0]! term body ∧
      IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx event.block record.inst
        (0,initial 3,Clif.Mem.empty) (1,after,Clif.Mem.empty) ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed event.ctx (initial 3)) Arm.ArmState.default = some (.fall ρ w) ∧
      after.regs 100 = some ⟨.i64,2⟩ ∧ event.ctx.valueReg? 7 = some (.vreg key .int) ∧
      VHolds ⟨.i64,7⟩ (ρ (aliasNum result.final.alias key)) ∧
      Inherited.CarryRel function result event.ctx event.block (fun _ _ _ => True) (fun x => x = 7)
        record.input (1,after,Clif.Mem.empty) ρ w := by
  obtain ⟨input⟩ := inputs
  have current : input.record.inst = blockStart function input.event.block+0 := by rw [input.current,input.atBlock]; rfl
  have source := LocalBody.actual_local_source_step input.run input.events input.split
    (record := input.record) (j := 0) (stm := ⟨[100],.div .udiv .i64 7 31⟩) rfl current True.intro
    (env := Clif.Env.empty) (cp := {funcs := []})
    (s := ⟨initial 3,[],Clif.Mem.empty⟩) (t := ⟨after,[],Clif.Mem.empty⟩) rfl rfl
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  obtain ⟨ρ,w,executed,post⟩ := Inherited.division_scan_carry_fall_refines input.run input.scope input.dominated
    input.events input.records input.split rfl current .udiv input.source input.clif input.results rfl input.mapped
    input.recorded input.emitted (carry_available input)
    (refines_csem (fun _ => False) ⟨0,0⟩ X) stable
    (0,initial 3,Clif.Mem.empty) (1,after,Clif.Mem.empty) source
    (entrySeed input.event.ctx (initial 3)) Arm.ArmState.default (entry_carry input 3 Arm.ArmState.default)
  obtain ⟨key,mapped,value⟩ := post.2 7 rfl ⟨.i64,7⟩ rfl
  exact ⟨input.result,input.event,input.record,input.term,input.body,ρ,w,key,input.run,input.scope,input.dominated,
    input.events,input.records,input.split,source,executed,rfl,mapped,value,post⟩

/-- The same actual compiler record and executable entry also inhabit the
zero-divisor trap path under the extended carry invariant. -/
theorem executable_division_zero_carry_witness (X : ExtSem) :
    ∃ result event record term body,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      SourceBodySplit function event function.blocks[0]! term body ∧
      Clif.enterFunc function [⟨.i64,7⟩,⟨.i64,0⟩] Clif.Mem.empty = .ok (initial 0,Clif.Mem.empty) ∧
      Clif.step Clif.Env.empty {funcs := []} ⟨initial 0,[],Clif.Mem.empty⟩ = .trapped .intDivz ∧
      Inherited.CarryRel function result event.ctx event.block (fun _ _ _ => True) (fun x => x = 7)
        record.output.state (0,initial 0,Clif.Mem.empty) (entrySeed event.ctx (initial 0)) Arm.ArmState.default ∧
      TrapRun (csem (fun _ => False) ⟨0,0⟩ X)
        (record.output.emitted.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed event.ctx (initial 0)) Arm.ArmState.default .intDivz := by
  obtain ⟨input⟩ := inputs
  have current : input.record.inst = blockStart function input.event.block+0 := by rw [input.current,input.atBlock]; rfl
  have failed := LocalBody.actual_local_source_trap input.run input.events input.split
    (j := 0) (stm := ⟨[100],.div .udiv .i64 7 31⟩) rfl True.intro
    (env := Clif.Env.empty) (cp := {funcs := []}) (s := ⟨initial 0,[],Clif.Mem.empty⟩) rfl
    (show Clif.step Clif.Env.empty {funcs := []} ⟨initial 0,[],Clif.Mem.empty⟩ = .trapped .intDivz from rfl)
  have trapped := Inherited.division_scan_carry_trap_refines input.run input.scope input.dominated
    input.events input.records input.split rfl current input.source input.clif input.results rfl input.mapped
    input.recorded input.emitted (refines_csem (fun _ => False) ⟨0,0⟩ X)
    (0,initial 0,Clif.Mem.empty) .intDivz (by simpa only [← current] using failed)
    (entrySeed input.event.ctx (initial 0)) Arm.ArmState.default (entry_carry input 0 Arm.ArmState.default)
  exact ⟨input.result,input.event,input.record,input.term,input.body,input.run,input.scope,input.dominated,
    input.events,input.records,input.split,rfl,rfl,entry_carry input 0 Arm.ArmState.default,trapped⟩

private theorem singleton_scan {exec : Nat → State → Except String Scan}
    {state : State} {body : BlockScan} {record : ScanRecord}
    (scanned : ScansSpec exec [record.inst] state body) (member : record ∈ body.records) :
    body.state = record.output.state ∧ state = record.input ∧ body.code = record.output.emitted := by
  cases scanned with
  | cons head tail =>
    cases tail
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    refine ⟨(congrArg (fun r : ScanRecord => r.output.state) member).symm,
      (congrArg ScanRecord.input member).symm,?_⟩
    simpa only [Array.empty_append] using (congrArg (fun r : ScanRecord => r.output.emitted) member).symm

private theorem body_shape (input : Inputs) :
    input.body.state = input.record.output.state ∧ input.term.output.state = input.record.input ∧
      input.body.code = input.record.output.emitted := by
  have indices : sourceBodyIndices function input.event.block function.blocks[0]! = [input.record.inst] := by
    rw [input.atBlock,input.current]
    rfl
  have member := input.records
  rw [input.split.records] at member
  have present : input.record ∈ input.body.records := by
    rcases List.mem_cons.mp member with same | member
    · have equality := congrArg ScanRecord.inst same
      rw [input.current,input.split.termInst,input.split.termIndex,input.atBlock] at equality
      cases equality
    · exact member
  apply singleton_scan (by rw [← indices]; exact input.split.scanned) present

private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,
    (∃ ty imm,stm.inst = .iconst ty imm) ∨ (∃ op ty x y,stm.inst = .div op ty x y) ∨ stm.inst = .nop := by
  intro b member stm present
  change b ∈ [function.blocks[0]!] at member
  cases List.mem_singleton.mp member
  change stm ∈ [⟨[100],.div .udiv .i64 7 31⟩] at present
  cases List.mem_singleton.mp present
  exact Or.inr (Or.inl ⟨.udiv,.i64,7,31,rfl⟩)

/-- Whole-body composition is inhabited on the same actual compiler run for
both normal division and its zero-divisor trap, without any new finite fact. -/
theorem executable_division_body_carry_witness (X : ExtSem) :
    ∃ result event record term body ρ w,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      SourceBodySplit function event function.blocks[0]! term body ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed event.ctx (initial 3)) Arm.ArmState.default = some (.fall ρ w) ∧
      Inherited.CarryRel function result event.ctx event.block (fun _ _ _ => True) (fun x => x = 7)
        term.output.state (1,after,Clif.Mem.empty) ρ w ∧
      TrapRun (csem (fun _ => False) ⟨0,0⟩ X)
        (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
        (entrySeed event.ctx (initial 0)) Arm.ArmState.default .intDivz := by
  obtain ⟨input⟩ := inputs
  have shape := body_shape input
  have current : input.record.inst = blockStart function input.event.block+0 := by rw [input.current,input.atBlock]; rfl
  have indices : (sourceBodyIndices function input.event.block function.blocks[0]!).reverse = [input.record.inst] := by
    rw [input.atBlock,input.current]
    rfl
  have source := LocalBody.actual_local_source_step input.run input.events input.split
    (record := input.record) (j := 0) (stm := ⟨[100],.div .udiv .i64 7 31⟩) rfl current True.intro
    (env := Clif.Env.empty) (cp := {funcs := []})
    (s := ⟨initial 3,[],Clif.Mem.empty⟩) (t := ⟨after,[],Clif.Mem.empty⟩) rfl rfl
  have steps : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx input.event.block)
      (sourceBodyIndices function input.event.block function.blocks[0]!).reverse
      (0,initial 3,Clif.Mem.empty) (1,after,Clif.Mem.empty) := by
    rw [indices]
    exact .cons source (.nil _)
  have failed := LocalBody.actual_local_source_trap input.run input.events input.split
    (j := 0) (stm := ⟨[100],.div .udiv .i64 7 31⟩) rfl True.intro
    (env := Clif.Env.empty) (cp := {funcs := []}) (s := ⟨initial 0,[],Clif.Mem.empty⟩) rfl
    (show Clif.step Clif.Env.empty {funcs := []} ⟨initial 0,[],Clif.Mem.empty⟩ = .trapped .intDivz from rfl)
  have failures : SourceTrapSteps
      (IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx input.event.block)
      (LocalBody.IndexedSourceTrap Clif.Env.empty {funcs := []} function input.event.ctx input.event.block)
      (sourceBodyIndices function input.event.block function.blocks[0]!).reverse
      (0,initial 0,Clif.Mem.empty) .intDivz := by
    rw [indices]
    exact .here (by simpa only [← current] using failed)
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  have formats : ∀ b ∈ function.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst := by
    intro block member stm present
    rcases family block member stm present with ⟨ty,imm,shape⟩ | ⟨op,ty,x,y,shape⟩ | shape
    all_goals simp [CastComplete.MemoryFormat,shape,instNames]
  have bodyRefines := Inherited.constant_division_body_carry_refines_local input.run input.scope input.dominated input.events
    input.split formats (family _ (List.mem_of_getElem? input.split.block)) (carry_available input) (refines_csem (fun _ => False) ⟨0,0⟩ X)
    (driverSem_csem (fun _ => False) ⟨0,0⟩ X) stable (env := Clif.Env.empty) (cp := {funcs := []})
  obtain ⟨ρ,w,executed,post⟩ := bodyRefines.1 _ _ steps _ _
    (by simpa only [shape.1] using entry_carry input 3 Arm.ArmState.default)
  have trapped := bodyRefines.2 _ _ failures _ _
    (by simpa only [shape.1] using entry_carry input 0 Arm.ArmState.default)
  exact ⟨input.result,input.event,input.record,input.term,input.body,ρ,w,input.run,input.scope,input.dominated,
    input.events,input.records,input.split,executed,post,trapped⟩

end Backend.Stock.Proof.InheritedDivisionWitness
