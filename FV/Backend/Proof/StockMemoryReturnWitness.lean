import FV.Backend.Proof.StockMemoryReturnRefines
import FV.Backend.Proof.StockMemoryAutoScan
import FV.Backend.Proof.StockMemoryBodyFixture
import FV.Backend.Proof.StockMemorySelectedWitness
import FV.Backend.Proof.RefinesCSem

namespace Backend.Stock.Memory.LoadFixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
private def initial : Clif.State := ⟨{frame with body := [⟨[2],.load .load .i32 flags 0 0⟩]},[],heap⟩
private def registers (_ : Nat) : CV := ofX 4096

private theorem family : ∀ stm ∈ function.blocks[1]!.body,OrdinaryBody.OrdinaryInst stm.inst := by
  intro stm member
  have equal := List.mem_singleton.mp member
  subst stm
  constructor
  · intro fn args impossible; cases impossible
  · intro sig callee args impossible; cases impossible

private theorem before_only_pointer (ctx : Ctx) (x : Nat)
    (available : x ∈ availOf function (availIn function ctx) 1 0) : x = 0 := by
  obtain ⟨which,_⟩ := (mem_av (show function.blocks[1]? = some function.blocks[1]! from rfl)).mp available
  rcases which with parameter | incoming | ⟨j,stm,earlier,statement,defined⟩
  · change x ∈ ([] : List Nat) at parameter; cases parameter
  · have out := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).out 1 x incoming 0 (by decide +kernel)
    rcases out with parameter | defined | entry
    · simpa [parsOf,function] using parameter
    · simp [defsOf,function] at defined
    · have impossible := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand 0 x entry
      omega
  · omega

private theorem defined (input : RecordInput) : SourceDefinedAt function input.result.ctx input.event.block 0 initial.frame := by
  intro x available
  have equal := before_only_pointer input.result.ctx x (by simpa only [input.atBlock] using available)
  subst x
  exact ⟨_,rfl⟩

private theorem full_dfg (input : RecordInput) : DFGCons input.event.ctx initial.frame := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases zero : x = 0
    · subst x; rw [input.parameter] at defined; cases defined
    · simp [initial,frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup
  · intro x t v typed lookup
    by_cases zero : x = 0
    · subst x
      have pointer := (stock_lower_record_context input.run scope input.events).1.addr64 _ _ _ 0 input.source input.clif rfl
      have equal := Option.some.inj (pointer.symm.trans typed)
      subst t
      cases lookup
      rfl
    · simp [initial,frame,Clif.Regs.set,Clif.Regs.empty,zero] at lookup

private theorem guarded (input : RecordInput) :
    GuardedScanRel function input.result input.event.ctx 1 (relation.holds function)
      input.event.output.state (0,initial.frame,heap) registers world := by
  have required := stock_lower_load_operand_coverage input.run scope dominated input.events input.records
    (bi := 1) (j := 0) (b := function.blocks[1]!) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    rfl rfl input.current input.source input.clif input.results input.mapped input.parameter input.pointer
    input.recorded input.emitted input.selected
  have frameEq : restrict initial.frame (availOf function (availIn function input.result.ctx) 1 0) = initial.frame := by
    unfold restrict
    congr 1
    funext y
    by_cases zero : y = 0
    · subst y; simp only [required.2,ite_true]; rfl
    · simp [initial,frame,Clif.Regs.set,Clif.Regs.empty,zero]
  refine ⟨rfl,?_,memory_world,?_⟩
  · rw [frameEq]; exact full_dfg input
  · intro y required value lookup
    have zero := before_only_pointer input.result.ctx y required.2
    subst y
    have equal : value = ⟨.i64,4096⟩ := Option.some.inj lookup.symm
    subst value
    exact ⟨192,input.pointer,rfl⟩

private theorem body_run (input : RecordInput) {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit function input.event function.blocks[1]! term body)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat} {isem : Backend.Proof.Sem}
    {MR : MemRelT} (stable : MRStable F MR) (memorySem : MemRefines F sb syms isem)
    (memoryOk : MemRelOk F sb syms function MR) {env : Clif.Env} {cp : Clif.Program} :
    ∀ s s',SourceSteps (IndexedSourceInst env cp function input.event.ctx input.event.block)
      ((List.range function.blocks[1]!.body.length).map (blockStart function input.event.block+·)) s s' →
      ∀ ρ w,GuardedScanRel function input.result input.event.ctx input.event.block MR input.event.output.state s ρ w →
        ∃ ρ' w',seqRun isem (body.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧
          GuardedScanRel function input.result input.event.ctx input.event.block MR term.output.state s' ρ' w' := by
  have normal := stock_lower_load_scan_fall_refines_auto input.run scope dominated input.events input.records
    (bi := input.event.block) (j := 0) (b := function.blocks[1]!) (stm := ⟨[2],.load .load .i32 flags 0 0⟩)
    split.block rfl (by rw [input.atBlock]; exact input.current)
    input.source input.clif input.results rfl input.mapped input.parameter input.pointer
    input.recorded input.emitted stable memorySem memoryOk (env := env) (cp := cp)
  have each : ∀ r ∈ body.records,ScanFallRefines (IndexedSourceInst env cp function input.event.ctx input.event.block)
      isem input.result.final.alias (GuardedScanRel function input.result input.event.ctx input.event.block MR) r := by
    intro r member
    have equal : r = input.record := by simpa only [input.body_records split,List.mem_singleton] using member
    subst r
    exact normal
  intro s s' source ρ w held
  apply split.scanned.fall_refines each s s'
  · simpa only [sourceBodyIndices,List.reverse_reverse] using source
  · simpa only [split.state] using held

/-- The real placed load-and-return block executes the nonzero heap read and
the actual ABI return. This starts at that block's body boundary; function-entry
control composition and production activation remain separate obligations. -/
theorem actual_load_return_block_witness (X : ExtSem) :
    ∃ (input : RecordInput) (label : Nat) (vb : VBlock) (pre post : Array MInst),
      input.result.code.blocks[label]? = some vb ∧
      vb.insts = pre ++ input.event.output.code.map (·.mapRegs
        (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))) ++ post ∧
      RunOkABI function input.result.code (csem relation.F ⟨0,0⟩ X) (relation.holds function)
        initial.frame.slots ⟨label,pre.size,registers,world⟩ (.returned [⟨.i32,2779096485⟩] heap) := by
  obtain ⟨input⟩ := record_input
  obtain ⟨term,body,split⟩ := input.body_split
  obtain ⟨label,vb,pre,post,placed,code⟩ := stock_lower_block_scan_code input.run input.events
  have bodyRun := body_run input split (E2E.mrStable_holds relation function)
    (memRefines_csem relation.F ⟨0,0⟩ X rfl (fun _ _ h => by cases h)) (E2E.memRelOk_holds relation function)
    (env := Clif.Env.empty) (cp := {funcs := []})
  have before : GuardedScanRel function input.result input.event.ctx input.event.block (relation.holds function)
      input.event.output.state (0,initial.frame,heap) registers world := by
    simpa only [input.atBlock] using guarded input
  have finished := OrdinaryBody.actual_ordinary_return_refines_at input.run scope dominated rfl family rfl
    input.events split (s := initial) rfl rfl rfl rfl (defined input)
    (show Clif.runLoop Clif.Env.empty {funcs := []} 2 initial = .returned [⟨.i32,2779096485⟩] heap from rfl)
    (refines_csem relation.F ⟨0,0⟩ X) (E2E.mrStable_holds relation function) bodyRun placed code registers world before
  exact ⟨input,label,vb,pre,post,placed,code,finished⟩

end Backend.Stock.Memory.LoadFixture
