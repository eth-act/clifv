import FV.Backend.Proof.StockMaskBlockRefines
import FV.Backend.Proof.StockQuietBlockWitness
import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.StockEntryPrelude
import FV.Backend.Proof.MemRefines
import FV.Backend.Proof.RefinesCSem
import FV.E2E.RegLevelDriverSem

namespace Backend.Stock.Proof.MaskBlockWitness
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.lower Stock.runTerm

abbrev function := QuietBlockWitness.function

private theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have all : function.blocks.all (fun b => b.body.all Stock.Scalar.maskMixedBodyEligible) = true := by
    decide +kernel
  intro b member stm present
  exact Stock.Scalar.maskMixedBodyEligible_sound
    (List.all_eq_true.mp (List.all_eq_true.mp all b member) stm present)

-- witness: native_decide (fixed original input dominance only)
private theorem dominated : Dominated function := dominated_of (by native_decide)

private theorem scan_has_index {exec : Nat → State → Except String Scan}
    {indices : List Nat} {initial : State} {body : BlockScan}
    (scanned : ScansSpec exec indices initial body) {i : Nat} (inside : i ∈ indices) :
    ∃ record ∈ body.records,record.inst = i := by
  induction scanned with
  | nil => cases inside
  | cons head rest ih =>
    rcases List.mem_cons.mp inside with rfl | member
    · exact ⟨_,List.mem_cons_self ..,rfl⟩
    · obtain ⟨record,found,index⟩ := ih member
      exact ⟨record,List.mem_cons_of_mem _ found,index⟩

/-- The actual second original block, containing a colored division and a
bmask, inhabits the generalized family-record contract. -/
theorem actual_family_records_witness : ∃ result event term body,
    Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
    event ∈ result.blockScans.toList ∧ event.block = 1 ∧
    SourceBodySplit function event function.blocks[1]! term body ∧
    ∀ record ∈ body.records,MaskBody.Record function event.ctx event.block record := by
  obtain ⟨result,event,record,run,scope,events,block,rest⟩ := QuietBlockWitness.actual_block_record_witness
  obtain ⟨term,body,split,records⟩ := MaskBody.actual_families_at_block run scope family events
    (b := function.blocks[1]!) (by rw [block]; rfl)
  exact ⟨result,event,term,body,run,scope,dominated,events,block,split,records⟩

/-- A real zero-result nop in the entry block is present in the actual scan
and omitted even though a different block contains a mandatory division. -/
theorem actual_nop_record_witness : ∃ result event term body record step,
    Stock.lower function = .ok result ∧ event ∈ result.blockScans.toList ∧ event.block = 0 ∧
    SourceBodySplit function event function.blocks[0]! term body ∧ record ∈ body.records ∧
    record.inst = 1 ∧ record.output.step = some step ∧ step.decision = .omitted := by
  obtain ⟨result,oldEvent,oldRecord,run,scope,rest⟩ := QuietBlockWitness.actual_block_record_witness
  obtain ⟨ranges,params,before,data,core,raw,vb,sizes,build,coreRun,assembled,events,placed,code⟩ :=
    stock_lower_entry_assembly run scope
  have zero : core.scan.block = 0 := (stock_lowerBlockCore_scanOrigin coreRun).2.2.1
  have block : function.blocks[core.scan.block]? = some function.blocks[0]! := by rw [zero]; rfl
  obtain ⟨term,body,split,records⟩ := MaskBody.actual_families_at_block run scope family events block
  obtain ⟨record,member,index⟩ := scan_has_index split.scanned (i := 1) (by rw [zero]; decide)
  have current : record.inst = blockStart function core.scan.block+1 := by rw [index,zero]; rfl
  obtain ⟨step,recorded,omitted⟩ := MaskBody.actual_nop_record_at_block run scope events split member
    (stm := ⟨[],.nop⟩) (j := 1) rfl current rfl
  exact ⟨result,core.scan,term,body,record,step,run,events,zero,split,member,index,recorded,omitted⟩

private def zero : Clif.Val := ⟨.i64,0⟩
private def frameAt (denominator : BitVec 64) : Clif.Frame := {
  func := function
  regs := (Clif.Regs.empty.set 1 zero).set 6 ⟨.i64,denominator⟩
  slots := []
  body := function.blocks[0]!.body
  term := function.blocks[0]!.term }

private abbrev frame := frameAt 0

private def initialWorld (denominator : BitVec 64) : Arm.ArmState :=
  Arm.write_base_gpr 0#5 0 (Arm.write_base_gpr 1#5 denominator Arm.ArmState.default)

private theorem initial_arguments (denominator : BitVec 64) :
    ArgsAtEntry (fun _ => False) function.sig [zero,⟨.i64,denominator⟩] (initialWorld denominator) := by
  intro loc value member
  change (loc,value) ∈ [(.reg (.x 0),zero),(.reg (.x 1),⟨.i64,denominator⟩)] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same | same <;> cases same
  · simp only [VHolds,regVal,initialWorld,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    rfl
  · simp only [VHolds,regVal,initialWorld,Arm.r,Arm.read_base_gpr,Arm.write_base_gpr,
      Arm.read_store,Arm.write_store,rnum]
    change (denominator.setWidth 128).setWidth 64 = denominator
    rw [BitVec.setWidth_setWidth_of_le _ (by decide),BitVec.setWidth_eq]

/-- Executable original entry and the later-block zero-divisor trap are
inhabited independently of any machine or record premises. -/
theorem later_source_trap_witness :
    Clif.enterFunc function [zero,zero] Clif.Mem.empty = .ok (frame,Clif.Mem.empty) ∧
    Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨frame,[],Clif.Mem.empty⟩ = .trapped .intDivz := by
  exact ⟨rfl,rfl⟩

/-- Original ABI entry supplies a genuine guarded machine input to the
first block. The source trap occurs later, after the current body and jump. -/
theorem executable_later_trap_witness (X : ExtSem) :
    ∃ result event term body world ρ,
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ event.block = 0 ∧
      SourceBodySplit function event function.blocks[0]! term body ∧
      ∃ t left,left+2 = 4 ∧ Clif.runLoop Clif.Env.empty {funcs := []} left t = .trapped .intDivz ∧
        t.frame.body = [] ∧
        ∃ ρ' w',seqRun (csem (fun _ => False) ⟨0,0⟩ X)
          (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
              some (.fall ρ' w') ∧
          GuardedScanRel function result event.ctx event.block (fun _ _ _ => True)
            term.output.state (2,t.frame,t.mem) ρ' w' := by
  obtain ⟨result,oldEvent,oldRecord,run,scope,rest⟩ := QuietBlockWitness.actual_block_record_witness
  have entered := SourceEntry.of_enterFunc later_source_trap_witness.1
  let initial := initialWorld 0
  have arguments := initial_arguments 0
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) := by
    exact memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (by intro n b h; cases h)
  obtain ⟨event,vb,prelude,chunk,ρ,world,events,atEntry,placed,pieces,preludeRun,memory,values,same,after⟩ :=
    stock_lower_entry_prelude_refines_frame run scope dominated (cm := Clif.Mem.empty) entered
      (driverSem_csem (fun _ => False) ⟨0,0⟩ X) memorySem stable (w := initial) trivial arguments
  have held := stock_lower_entered_values_guarded_frame run scope dominated events (cm := Clif.Mem.empty) entered values
    event.output.state (MR := fun _ _ _ => True) world trivial
  have block : function.blocks[event.block]? = some function.blocks[0]! := by rw [atEntry]; rfl
  obtain ⟨term,body,split,normal,trapping⟩ := MaskBody.actual_body_refines_at_block run scope dominated
    family events block (refines_csem (fun _ => False) ⟨0,0⟩ X)
    (driverSem_csem (fun _ => False) ⟨0,0⟩ X) stable
    (env := Clif.Env.empty) (cp := {funcs := []})
  rcases LocalBody.actual_local_source_trap_or_continue run events split
    (b := function.blocks[0]!) (family := by
      intro stm member
      change stm ∈ [⟨[100],.iconst .i64 0⟩,⟨[],.nop⟩] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      · rfl
      · exact True.intro)
    (j := 0) (s := ⟨frame,[],Clif.Mem.empty⟩) (by omega) rfl later_source_trap_witness.2 with
      failed | ⟨t,left,total,continues,empty,steps,frameEq⟩
  · -- These two actual entry instructions cannot trap; the real trap is in block one.
    cases failed with
    | here failed =>
      obtain ⟨_,info,inst,tail,found,clif,remaining,trapped⟩ := failed
      change frame.body = ⟨info.results,inst⟩ :: tail at remaining
      have head := List.cons.inj (by simpa only [frame,frameAt,function,QuietBlockWitness.function,List.getElem!_cons_zero] using remaining)
      have instruction := congrArg Clif.Stmt.inst head.1
      simp only at instruction
      subst inst
      rw [LocalBody.local_outcome (show LocalBody.LocalInst (.iconst .i64 0) from rfl)] at trapped
      cases trapped
    | next first tail =>
      cases tail with
      | here failed =>
        obtain ⟨_,info,inst,rest,found,clif,remaining,trapped⟩ := failed
        -- The indexed original nop has no trapping evaluation.
        exact False.elim (by
          obtain ⟨index,advanced,step⟩ := first
          obtain ⟨info0,inst0,vs,regs,rest0,source0,original0,remaining0,evaluated,written,updated⟩ := step
          have restEq : rest0 = [⟨[],.nop⟩] := by
            change [⟨[100],.iconst .i64 0⟩,⟨[],.nop⟩] = ⟨info0.results,inst0⟩ :: rest0 at remaining0
            exact (List.cons.inj remaining0).2.symm
          rw [updated,restEq] at remaining
          have head := List.cons.inj remaining
          have instruction := congrArg Clif.Stmt.inst head.1
          simp only at instruction
          subst inst
          rw [LocalBody.local_outcome (show LocalBody.LocalInst .nop from True.intro)] at trapped
          cases trapped)
      | next _ tail => cases tail
  · have bodyLength : function.blocks[0]!.body.length = 2 := rfl
    rw [bodyLength] at steps
    obtain ⟨ρ',w',executed,post⟩ := normal (0,frame,Clif.Mem.empty) (2,t.frame,t.mem)
      (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range,bodyLength] using steps) ρ world held
    exact ⟨result,event,term,body,world,ρ,run,scope,dominated,events,atEntry,split,
      t,left,by change left+2 = 4 at total; exact total,continues,empty,ρ',w',executed,post⟩

/-- A genuine returning two-block run supplies the complete first-body machine
contract from original ABI entry. The terminator continuation is retained. -/
theorem executable_return_witness (X : ExtSem) :
    ∃ result event term body world ρ t left ρ' w',
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ event.block = 0 ∧
      SourceBodySplit function event function.blocks[0]! term body ∧
      left+2 = 6 ∧ Clif.runLoop Clif.Env.empty {funcs := []} left t = .returned [zero] Clif.Mem.empty ∧
      t.frame.body = [] ∧
      seqRun (csem (fun _ => False) ⟨0,0⟩ X)
        (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
            some (.fall ρ' w') ∧
      GuardedScanRel function result event.ctx event.block (fun _ _ _ => True)
        term.output.state (2,t.frame,t.mem) ρ' w' := by
  obtain ⟨result,oldEvent,oldRecord,run,scope,rest⟩ := QuietBlockWitness.actual_block_record_witness
  have entered : Clif.enterFunc function [zero,⟨.i64,1⟩] Clif.Mem.empty =
      .ok (frameAt 1,Clif.Mem.empty) := rfl
  have returned : Clif.runLoop Clif.Env.empty {funcs := []} 6 ⟨frameAt 1,[],Clif.Mem.empty⟩ =
      .returned [zero] Clif.Mem.empty := rfl
  have stable : MRStable (fun _ => False) (fun _ _ _ => True) := by intro _ _ _ _ _ _; trivial
  have memorySem : MemRefines (fun _ => False) 0 (fun _ => none) (csem (fun _ => False) ⟨0,0⟩ X) :=
    memRefines_csem (fun _ => False) ⟨0,0⟩ X rfl (fun _ _ h => by cases h)
  obtain ⟨event,vb,prelude,chunk,ρ,world,events,atEntry,placed,pieces,preludeRun,memory,values,same,after⟩ :=
    stock_lower_entry_prelude_refines_frame run scope dominated (cm := Clif.Mem.empty) (SourceEntry.of_enterFunc entered)
      (driverSem_csem (fun _ => False) ⟨0,0⟩ X) memorySem stable trivial (initial_arguments 1)
  have held := stock_lower_entered_values_guarded_frame run scope dominated events
    (cm := Clif.Mem.empty) (SourceEntry.of_enterFunc entered) values
    event.output.state (MR := fun _ _ _ => True) world trivial
  obtain ⟨term,body,split,t,left,total,continues,empty,frameEq,ρ',w',executed,post⟩ :=
    MaskBody.executable_body_return_at_block run scope dominated family events
      (b := function.blocks[0]!) (by rw [atEntry]; rfl)
      (s := ⟨frameAt 1,[],Clif.Mem.empty⟩) rfl returned
      (refines_csem (fun _ => False) ⟨0,0⟩ X) (driverSem_csem (fun _ => False) ⟨0,0⟩ X) stable held
  exact ⟨result,event,term,body,world,ρ,t,left,ρ',w',run,scope,dominated,events,atEntry,split,
    total,continues,empty,executed,post⟩

end Backend.Stock.Proof.MaskBlockWitness
