import FV.Backend.Proof.StockScalarCheck
import FV.Backend.Proof.StockScalarContract
import FV.Backend.Proof.StockDivReturnRefines
import FV.Backend.Proof.StockLocalSourceExecution
import FV.Backend.Proof.StockPureNotrap
import FV.Backend.Proof.StockScanSemantics
import FV.Backend.Proof.IselCmpDiv
import FV.Backend.Proof.StockDivBodyRefines
import FV.Backend.Proof.StockHighMulBodyRefines
import FV.Backend.Proof.StockGuardedOmission
import FV.Backend.Proof.StockPureBodyFamilies
import FV.Backend.Proof.StockPureSourceColors
import FV.Backend.Proof.StockPureDriverUnsunk
import FV.Backend.Proof.StockBlockScan

/-! Generic prefix/trap composition for the next mixed-body delivery.
No purity, unchanged-world or externally supplied record assumptions enter a
source domain: local obligations are internal proof-composition interfaces. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A finite original source prefix reaches an instruction's genuine trap. -/
inductive SourceTrapSteps {S : Type} (step : Nat → S → S → Prop)
    (trap : Nat → S → Clif.TrapCode → Prop) : List Nat → S → Clif.TrapCode → Prop where
  | here {i : Nat} {rest : List Nat} {s : S} {code : Clif.TrapCode}
      (failed : trap i s code) : SourceTrapSteps step trap (i :: rest) s code
  | next {i : Nat} {rest : List Nat} {s t : S} {code : Clif.TrapCode}
      (head : step i s t) (tail : SourceTrapSteps step trap rest t code) :
      SourceTrapSteps step trap (i :: rest) s code

private theorem sourceTrapSteps_append {S : Type} {step : Nat → S → S → Prop}
    {trap : Nat → S → Clif.TrapCode → Prop} {xs ys : List Nat} {s : S} {code : Clif.TrapCode} :
    SourceTrapSteps step trap (xs ++ ys) s code ↔
      SourceTrapSteps step trap xs s code ∨
        ∃ t, SourceSteps step xs s t ∧ SourceTrapSteps step trap ys t code := by
  induction xs generalizing s with
  | nil =>
    constructor
    · intro h; exact Or.inr ⟨s,.nil s,h⟩
    · rintro (impossible | ⟨t,steps,failed⟩)
      · cases impossible
      · cases steps; exact failed
  | cons i xs ih =>
    constructor
    · intro h
      cases h with
      | here failed => exact Or.inl (.here failed)
      | next head tail =>
        rcases ih.mp tail with failed | ⟨t,front,back⟩
        · exact Or.inl (.next head failed)
        · exact Or.inr ⟨t,.cons head front,back⟩
    · rintro (failed | ⟨t,steps,back⟩)
      · cases failed with
        | here failed => exact .here failed
        | next head tail => exact .next head (ih.mpr (Or.inl tail))
      · cases steps with
        | cons head tail => exact .next head (ih.mpr (Or.inr ⟨t,tail,back⟩))

/-- A fall-through prefix can change the world before a real trap. -/
theorem trapRun_seq_prefix {isem : Backend.Proof.Sem} {first rest : List MInst}
    {ρ ρ' : Nat → CV} {w w' : Arm.ArmState} {code : Clif.TrapCode}
    (executed : seqRun isem first ρ w = some (.fall ρ' w'))
    (failed : TrapRun isem rest ρ' w' code) : TrapRun isem (first ++ rest) ρ w code := by
  obtain ⟨offset,i,ops,regs,before,outs,after,run,coded⟩ := failed
  exact ⟨_,i,ops,regs,before,outs,after,seqRun_append_fall_stop isem executed run,coded⟩

/-- The actual selected chunk refines a trapping source instruction. -/
def ScanTrapRefines {S : Type} (sourceTrap : Nat → S → Clif.TrapCode → Prop)
    (sem : Backend.Proof.Sem) (aliases : Array (Option Nat))
    (rel : State → S → (Nat → CV) → Arm.ArmState → Prop) (record : ScanRecord) : Prop :=
  ∀ s code, sourceTrap record.inst s code → ∀ ρ w,
    rel record.output.state s ρ w →
      TrapRun sem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ w code

/-- Real backward scan chunks compose in forward order through the first
source trap. Later chunks do not execute. Source and world relations may carry
memory effects; no pure-run or no-trap shortcut is used. -/
theorem ScansSpec.trap_refines {S : Type} {exec : Nat → State → Except String Scan}
    {source : Nat → S → S → Prop} {sourceTrap : Nat → S → Clif.TrapCode → Prop}
    {sem : Backend.Proof.Sem} {aliases : Array (Option Nat)}
    {rel : State → S → (Nat → CV) → Arm.ArmState → Prop}
    {indices : List Nat} {input : State} {output : BlockScan}
    (scanned : ScansSpec exec indices input output)
    (normal : ∀ r ∈ output.records, ScanFallRefines source sem aliases rel r)
    (trapping : ∀ r ∈ output.records, ScanTrapRefines sourceTrap sem aliases rel r) :
    ∀ s code, SourceTrapSteps source sourceTrap indices.reverse s code → ∀ ρ w,
      rel output.state s ρ w →
      TrapRun sem (output.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ w code := by
  induction scanned with
  | nil input =>
    intro s code failed
    cases failed
  | @cons i indices input scan tail head rest ih =>
    intro s code failed ρ w held
    have split : SourceTrapSteps source sourceTrap (indices.reverse ++ [i]) s code := by
      simpa only [List.reverse_cons] using failed
    rcases sourceTrapSteps_append.mp split with front | ⟨mid,front,last⟩
    · have failed := ih (fun r h => normal r (List.mem_cons_of_mem _ h))
        (fun r h => trapping r (List.mem_cons_of_mem _ h)) s code front ρ w held
      simpa only [Array.toList_append,List.map_append] using failed.append
    · obtain ⟨ρ',w',executed,post⟩ := rest.fall_refines
        (fun r h => normal r (List.mem_cons_of_mem _ h)) s mid front ρ w held
      have terminal : sourceTrap i mid code := by
        cases last with
        | here failed => exact failed
        | next stepped impossible => cases impossible
      have failed := trapping ⟨i,input,scan⟩ (List.mem_cons_self ..) mid code terminal ρ' w' post
      simpa only [Array.toList_append,List.map_append] using trapRun_seq_prefix executed failed

end Backend.Stock.Proof
#print axioms Backend.Stock.Proof.trapRun_seq_prefix
#print axioms Backend.Stock.Proof.ScansSpec.trap_refines


/-! Extract a genuine trapped prefix from the original executable source.
This is independent of the single-division shape and preserves original input
values, memory and trap code. The eventual compiler domain derives its record
obligations internally. -/
namespace Backend.Stock.Proof.LocalBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The previous pure family remains a local source family. -/
theorem LocalInst.of_pure {inst : Clif.Inst} (pure : pureInst inst = true) : LocalInst inst := by
  cases inst <;> simp_all [LocalInst,pureInst]

/-- A source position evaluates the actual installed original instruction to
its real trap. No success, nonzero, or no-overflow premise is introduced. -/
def IndexedSourceTrap (env : Clif.Env) (cp : Clif.Program) (f : Clif.Function)
    (ctx : Ctx) (bi i : Nat) (s : SourcePoint) (code : Clif.TrapCode) : Prop :=
  i = blockStart f bi + s.1 ∧ ∃ (info : IInfo) (inst : Clif.Inst) (rest : List Clif.Stmt),
    ctx.insts[i]? = some info ∧ info.clif = some inst ∧
    s.2.1.body = ⟨info.results,inst⟩ :: rest ∧
    instOutcome env cp s.2.1 s.2.2 inst = .trap code

private theorem local_step {env : Clif.Env} {cp : Clif.Program}
    {s : Clif.State} {stm : Clif.Stmt} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) (family : LocalInst stm.inst) :
    Clif.step env cp s = Clif.StepResult.ofRes (Clif.evalInst s.frame s.mem stm.inst)
      (fun (vs,cm) => Clif.continueWith s rest stm.results vs cm) := by
  cases shape : stm.inst <;> simp only [shape,LocalInst,pureInst] at family <;> try cases family
  all_goals unfold Clif.step; simp only [remaining,shape]

theorem local_outcome {env : Clif.Env} {cp : Clif.Program}
    {fr : Clif.Frame} {cm : Clif.Mem} {inst : Clif.Inst} (family : LocalInst inst) :
    instOutcome env cp fr cm inst = Clif.evalInst fr cm inst := by
  cases inst <;> simp only [LocalInst,pureInst] at family <;> try cases family
  all_goals rfl

/-- Original execution provides a real instruction trap at the actual source
metadata position, using the same source-results identity as normal execution. -/
theorem actual_local_source_trap {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (family : LocalInst stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {s : Clif.State} {rest : List Clif.Stmt}
    (remaining : s.frame.body = stm :: rest) {code : Clif.TrapCode}
    (trapped : Clif.step env cp s = .trapped code) :
    IndexedSourceTrap env cp f event.ctx event.block (blockStart f event.block+j)
      (j,s.frame,s.mem) code := by
  obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split
    (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl
  refine ⟨rfl,info,stm.inst,rest,source,clif,?_,?_⟩
  · rw [remaining,results]
  · rw [local_outcome family]
    rw [local_step remaining family] at trapped
    cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
    | trap c =>
      simp only [evaluated,Clif.StepResult.ofRes,Clif.StepResult.trapped.injEq] at trapped
      cases trapped
      rfl
    | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at trapped; cases trapped
    | ok pair =>
      obtain ⟨vs,cm⟩ := pair
      simp only [evaluated,Clif.StepResult.ofRes,Clif.continueWith] at trapped
      cases written : s.frame.regs.setMany stm.results vs <;> simp only [written] at trapped <;> cases trapped


/-- A real trapped original run supplies the complete executable prefix up to
its first trapping local instruction. The empty returned body cannot trap. -/
theorem actual_local_source_trap_execution {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body)
    (family : ∀ stm ∈ b.body, LocalInst stm.inst)
    {env : Clif.Env} {cp : Clif.Program} {fuel j : Nat} {s : Clif.State}
    (bound : j ≤ b.body.length) (remaining : s.frame.body = b.body.drop j)
    (callers : s.callers = []) {xs : List Nat} (ret : s.frame.term = .ret xs)
    {code : Clif.TrapCode} (trapped : Clif.runLoop env cp fuel s = .trapped code) :
    SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
      (IndexedSourceTrap env cp f event.ctx event.block)
      (List.range' (blockStart f event.block+j) (b.body.length-j)) (j,s.frame,s.mem) code := by
  induction fuel generalizing j s with
  | zero => cases trapped
  | succ fuel ih =>
    by_cases done : j = b.body.length
    · have empty : s.frame.body = [] := by simpa [done] using remaining
      exact False.elim (PureBody.pure_source_notrap (fuel+1) s callers
        (by simp [empty]) ret code trapped)
    · have inside : j < b.body.length := by omega
      let stm := b.body[j]
      have statement : b.body[j]? = some stm := List.getElem?_eq_getElem inside
      have head : s.frame.body = stm :: b.body.drop (j+1) := by
        rw [remaining,List.drop_eq_getElem_cons inside]
      have instFamily := family stm (List.mem_of_getElem? statement)
      have length : b.body.length-j = (b.body.length-(j+1))+1 := by omega
      rw [length,List.range'_succ]
      rw [Clif.runLoop_succ,local_step head instFamily] at trapped
      cases evaluated : Clif.evalInst s.frame s.mem stm.inst with
      | trap c =>
        simp only [evaluated,Clif.StepResult.ofRes,Clif.Outcome.trapped.injEq] at trapped
        cases trapped
        apply SourceTrapSteps.here
        apply actual_local_source_trap run events split statement instFamily head
        rw [local_step head instFamily,evaluated]
        rfl
      | stuck message => simp only [evaluated,Clif.StepResult.ofRes] at trapped; cases trapped
      | ok pair =>
        obtain ⟨vs,cm⟩ := pair
        simp only [evaluated,Clif.StepResult.ofRes,Clif.continueWith] at trapped
        cases written : s.frame.regs.setMany stm.results vs with
        | none => simp only [written] at trapped; cases trapped
        | some regs =>
          simp only [written] at trapped
          let t : Clif.State := {s with frame := {s.frame with regs,body := b.body.drop (j+1)},mem := cm}
          have next : Clif.step env cp s = .next t := by
            rw [local_step head instFamily,evaluated]
            simp only [Clif.StepResult.ofRes,Clif.continueWith,written]
            rfl
          have source := actual_local_source_step run events split
            (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl instFamily head next
          have tail := ih (s := t) (j := j+1) (by omega) rfl callers ret trapped
          have prefixStep := SourceTrapSteps.next source tail
          simpa only [Nat.add_assoc,Nat.add_comm 1 j] using prefixStep

end Backend.Stock.Proof.LocalBody
#print axioms Backend.Stock.Proof.LocalBody.actual_local_source_trap
#print axioms Backend.Stock.Proof.LocalBody.actual_local_source_trap_execution

namespace Backend.Stock.Proof.LocalBody
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem body_segment {vb : VBlock} {pre chunk post : Array MInst}
    (parts : vb.insts = pre ++ chunk ++ post) : SegAt vb pre.size chunk.toList := by
  intro k hk
  have bound : k < chunk.size := by simpa using hk
  rw [parts,Array.append_assoc,Array.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [Array.getElem?_append_left bound]
  simp [bound]

/-- Compose actual ABI materialization and a proved local body with a genuine
source trap. Family handlers are internal proof obligations; the resulting
production domain retains the original input and executable source run. -/
theorem actual_local_entry_trap_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (family : ∀ stm ∈ b.body, LocalInst stm.inst)
    {xs : List Nat} (ret : b.term = .ret xs)
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame}
    (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (bodyProvider : ∀ event, event ∈ result.blockScans.toList →
      ∃ term body, SourceBodySplit f event b term body ∧
        ∀ s code, SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
          (IndexedSourceTrap env cp f event.ctx event.block)
          ((List.range b.body.length).map (blockStart f event.block+·)) s code →
          ∀ ρ w, GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
            TrapRun isem (body.code.toList.map (·.mapRegs
              (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code)
    {w : Arm.ArmState} (memory : MR fr.slots cm w)
    (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ, VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code := by
  obtain ⟨event,vb,pre,chunk,ρ',w',events,zero,placed,pieces,execution,mem',values,same,
    after,bodyCode⟩ := stock_lower_entry_prelude_refines_frame run scope dominated entered driver
      memorySem stable memory arguments
  obtain ⟨term,body,split,bodyRun⟩ := bodyProvider event events
  have facts := entered
  obtain ⟨b',regs,entry,argTypes,paramTypes,set,frame⟩ := facts
  have sameBlock : b' = b := by
    have found : some b = some b' := by
      simpa only [Clif.Function.entry?,blocks,List.head?_cons] using entry
    exact Option.some.inj found.symm
  subst b'
  have sourceTrap := actual_local_source_trap_execution run events split family
    (s := ⟨fr,[],cm⟩) (j := 0) (by omega) (by rw [frame]; simp)
    rfl (by rw [frame]; exact ret) trapped
  have held := stock_lower_entered_values_guarded_frame run scope dominated events entered values
    event.output.state w' mem'
  have trap := bodyRun (0,fr,cm) code
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using sourceTrap) ρ' w' held
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have parts : vb.insts = pre ++ body.code.map (·.mapRegs resolve) ++
      (term.output.emitted.map (·.mapRegs resolve) ++ after) := by
    rw [pieces,bodyCode,split.code,Array.map_append]
    simp only [Array.append_assoc,resolve]
  have segment : SegAt vb pre.size (body.code.toList.map (·.mapRegs resolve)) := by
    simpa only [Array.toList_map] using body_segment parts
  have finished := DivBody.trapRun_at placed segment trap
  have room : pre.size < vb.insts.size := by
    obtain ⟨offset,i,ops,ρ1,w1,outs,final,traced,coded⟩ := trap
    obtain ⟨path,bound,atInst,rest⟩ := seqRun_stop_star placed segment traced
    have inside := (Array.getElem?_eq_some_iff.mp atInst).1
    omega
  have preSegment : SegAt vb 0 pre.toList := by
    intro k bounded
    have inside : k < pre.size := by simpa only [Array.length_toList] using bounded
    rw [Nat.zero_add,pieces,Array.getElem?_append_left inside]
    simp [inside]
  have path := seqRun_fall_star (vc := result.code) (sem := isem) placed preSegment
    (by simpa only [Nat.zero_add,Array.length_toList] using room) execution
  exact ⟨entrySeed event.ctx fr,finished.prefix (by simpa only [Nat.zero_add,Array.length_toList] using path)⟩
end Backend.Stock.Proof.LocalBody
#print axioms Backend.Stock.Proof.LocalBody.actual_local_entry_trap_refines_frame
namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
private abbrev ColorState := Array Nat × Array Nat × Array (List Nat) × Nat
private def bodyStep (start bi : Nat) (x : Clif.Stmt × Nat) (s : ColorState) : Id (ForInStep ColorState) :=
  if colored x.1.inst then
    pure (.yield (s.1.set! (start+x.2) bi,s.2.1.set! (start+x.2) s.2.2.2,
      s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2+1))
  else pure (.yield (s.1.set! (start+x.2) bi,s.2.1,
    s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2))
private theorem body_color_at (start bi q : Nat) (xs : List (Clif.Stmt × Nat))
    (separate : ∀ x ∈ xs, colored x.1.inst = true → start+x.2 ≠ q) (s : ColorState) :
    ((forIn xs s (bodyStep start bi)).run).2.1[q]! = s.2.1[q]! := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    have tail : ∀ y ∈ xs, colored y.1.inst = true → start+y.2 ≠ q :=
      fun y hy => separate y (List.mem_cons_of_mem _ hy)
    rw [List.forIn_cons]
    cases coloredHere : colored x.1.inst with
    | false =>
      simp only [bodyStep,coloredHere,Bool.false_eq_true,ite_false]
      exact ih tail _
    | true =>
      simp only [bodyStep,coloredHere,ite_true]
      change ((forIn xs (s.1.set! (start+x.2) bi,s.2.1.set! (start+x.2) s.2.2.2,
        s.2.2.1.set! (start+x.2) (instArgs x.1.inst),s.2.2.2+1) (bodyStep start bi)).run).2.1[q]! = s.2.1[q]!
      rw [ih tail]
      exact Array.getElem!_set!_ne _ _ _ _ (separate x (List.mem_cons_self ..) coloredHere)

/-- Only the selected source position must be quiet. Other instructions may
carry division/trap colors; their distinct indexed writes cannot color it. -/
theorem sourceMetadata_quiet_single_block (ctx : Ctx) (ranges : Array (Nat × Nat)) (b : Clif.Block)
    (blocks : ctx.func.blocks = [b]) (range : ranges[0]! = (0,b.body.length+1))
    {q : Nat} {stm : Clif.Stmt} (statement : b.body[q]? = some stm)
    (quiet : colored stm.inst = false) : (sourceMetadata ctx ranges).entryColor[q]! = 0 := by
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have sourceAt : b.body[q] = stm := by
    have found := List.getElem?_eq_getElem inside
    rw [statement] at found
    exact (Option.some.inj found).symm
  have separate : ∀ x ∈ b.body.zipIdx, colored x.1.inst = true → ranges[0]!.1+x.2 ≠ q := by
    intro x member coloredHere equal
    have index : x.2 = q := by simpa only [range,Nat.zero_add] using equal
    have item := (List.mem_zipIdx member).2.2
    simp only [Nat.sub_zero,index] at item
    have same : x.1 = stm := item.trans sourceAt
    rw [same,quiet] at coloredHere
    cases coloredHere
  have inner := body_color_at ranges[0]!.1 0 q b.body.zipIdx separate
    (Array.replicate ctx.insts.size 0,Array.replicate ctx.insts.size 0,
      Array.replicate ctx.insts.size [],0+1)
  simp only [sourceMetadata,blocks,List.zipIdx_cons,List.zipIdx_nil,
    List.forIn_cons,List.forIn_nil,Id.run_bind,Id.run_pure]
  change (((forIn b.body.zipIdx _ (bodyStep ranges[0]!.1 0)).run).2.1.set!
    (ranges[0]!.2-1) _)[q]! = 0
  have different : ranges[0]!.2-1 ≠ q := by rw [range]; simp only; omega
  rw [Array.getElem!_set!_ne _ _ _ _ different,inner]
  by_cases bound : q < ctx.insts.size <;> simp [getElem!_def,Array.getElem?_replicate,bound]

theorem buildCtx_quiet_single_block {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    {b : Clif.Block} (blocks : f.blocks = [b])
    {q : Nat} {stm : Clif.Stmt} (statement : b.body[q]? = some stm)
    (quiet : colored stm.inst = false) :
    initial.entryColor[q]! = 0 ∧ initial.sunk[q]! = false := by
  obtain ⟨original,st0,requests,oldBuild,_,finished⟩ := buildCtx_allocation build
  have spec := ctxSpec_of oldBuild
  have originalBlocks : original.func.blocks = [b] := by rw [spec.func]; exact blocks
  have range : ranges[0]! = (0,b.body.length+1) := by
    have found : f.blocks[0]? = some b := by rw [blocks]; rfl
    have r := spec.ranges 0 b found
    simp only [getElem!_def,r,Option.getD_some]
    simp [blockStart]
  have state := congrArg (fun p : Ctx × Array (Nat × Nat) × State => p.2.2) finished
  dsimp only at state
  rw [state]
  constructor
  · change (sourceMetadata original ranges).entryColor[q]! = 0
    exact sourceMetadata_quiet_single_block original ranges b originalBlocks range statement quiet
  · change (Array.replicate original.insts.size false)[q]! = false
    by_cases bound : q < original.insts.size <;>
      simp [getElem!_def,Array.getElem?_replicate,bound]


/-- Actual whole-driver unsunkness at one quiet source slot remains available
when other slots have division/trap colors. -/
theorem stock_lower_quiet_single_block_unsunk {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {b : Clif.Block} (blocks : f.blocks = [b])
    {q : Nat} {stm : Clif.Stmt} (statement : b.body[q]? = some stm)
    (quiet : colored stm.inst = false) :
    result.initial.entryColor[q]! = 0 ∧ result.final.sunk[q]! = false ∧
      ∀ event ∈ result.blockScans.toList, event.input.sunk[q]! = false ∧
        ∀ record ∈ event.output.records,
          record.input.sunk[q]! = false ∧ record.output.state.sunk[q]! = false := by
  have built : ∃ ctx ranges, Stock.buildCtx f = .ok (ctx,ranges,result.initial) := by
    have actual := run
    unfold Stock.lower at actual
    dsimp only at actual
    repeat' first
      | (solve | cases actual)
      | simp only [bind,Except.bind,pure,Except.pure] at actual
      | split at actual
    cases actual
    rename_i _ built hbuild _ order horder _ driver hdriver
    exact ⟨built.1,built.2.1,hbuild⟩
  obtain ⟨ctx,ranges,build⟩ := built
  obtain ⟨zero,safe⟩ := buildCtx_quiet_single_block build blocks statement quiet
  obtain ⟨final,events⟩ := stock_lower_zeroColorLe run
  refine ⟨zero,final.2 q zero safe,?_⟩
  intro event member
  obtain ⟨pre,records⟩ := events event member
  refine ⟨pre.2 q zero safe,?_⟩
  intro record retained
  obtain ⟨a,b⟩ := records record retained
  exact ⟨a.2 q zero safe,b.2 q zero safe⟩

end Backend.Stock.Proof.QuietSourceColors
#print axioms Backend.Stock.Proof.QuietSourceColors.sourceMetadata_quiet_single_block

#print axioms Backend.Stock.Proof.QuietSourceColors.buildCtx_quiet_single_block

#print axioms Backend.Stock.Proof.QuietSourceColors.stock_lower_quiet_single_block_unsunk

namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem records_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member

/-- One original quiet statement derives its actual omission/emission and
result mapping even when other source statements are colored. -/
theorem actual_quiet_source_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {term : ScanRecord} {body : BlockScan} (split : SourceBodySplit f event b term body)
    {record : ScanRecord} (member : record ∈ body.records)
    {j : Nat} {stm : Clif.Stmt} (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f event.block+j)
    (quiet : colored stm.inst = false)
    (single : (stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig))
      (f.sigDecls.lookup ·)).map List.length = some 1) :
    PureBody.SourceRecord f event.ctx event.block record := by
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have bi : event.block = 0 := by simpa using bound
  have current' : record.inst = j := by simpa [bi,blockStart] using current
  have inside := (List.getElem?_eq_some_iff.mp statement).1
  have ordinary : record.inst ≠ event.termInst := by
    rw [current',split.termIndex,bi]
    simp only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add]
    omega
  have preserved := (stock_lower_quiet_single_block_unsunk run blocks statement quiet).2.2 event events
  have safe : record.input.sunk[record.inst]! = false := by
    rw [current']
    exact (preserved.2 record (split.retained record member)).1
  have actual := records_execute split.scanned record member
  obtain ⟨step,recorded,decision⟩ := stock_ordinary_unsunk_decision safe ordinary actual
  have decided : step.decision = .omitted ∨ step.decision = .emitted := by
    rcases decision with omitted | remembered | emitted
    · exact Or.inl omitted
    · exact False.elim ((Coverage.lower_record_noOpportunistic scope run events
        (split.retained record member) recorded) remembered)
    · exact Or.inr emitted
  refine ⟨j,b,stm,split.block,statement,current,step,recorded,?_⟩
  rcases decided with omitted | emitted
  · exact Or.inl omitted
  · obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
    have inv := (stock_lower_record_context run scope events).1
    obtain ⟨tys,types,typed,arity⟩ := inv.resTys record.inst info stm.inst source clif
    rw [types] at single
    have length : info.results.length = 1 := arity.trans (Option.some.inj single)
    obtain ⟨x,infoResults⟩ : ∃ x, info.results = [x] := by
      cases values : info.results with
      | nil => simp [values] at length
      | cons x rest =>
        cases rest with
        | nil => exact ⟨x,rfl⟩
        | cons y tail => simp [values] at length
    obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan actual recorded emitted
    have atInst : event.ctx.insts[record.inst]! = info := by
      simp only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,source,Option.getD_some]
    obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun
      (by rw [atInst]; exact infoResults)
    obtain ⟨a,rfl⟩ := inv.valueReg x r mapped
    exact Or.inr ⟨emitted,info,x,a,source,clif,infoResults,results.symm.trans infoResults,mapped⟩
end Backend.Stock.Proof.QuietSourceColors
#print axioms Backend.Stock.Proof.QuietSourceColors.actual_quiet_source_record

namespace Backend.Stock.Proof.QuietSourceColors
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- Reuse all previously proved scalar-family handlers at one actual quiet
prefix record, while other source positions may contain real division. -/
theorem highmul_source_record_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {record : ScanRecord} (records : record ∈ event.output.records)
    {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi+j)
    (family : HighMulBody.Family stm.inst)
    (recordSource : PureBody.SourceRecord f event.ctx bi record)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  obtain ⟨j',b',stm',found,atStmt,indexed,step,recorded,decision⟩ := recordSource
  have sameB : b' = b := Option.some.inj (found.symm.trans block)
  subst b'
  have sameJ : j' = j := Nat.add_left_cancel (indexed.symm.trans current)
  subst j'
  have sameStmt : stm' = stm := Option.some.inj (atStmt.symm.trans statement)
  subst stm'
  rcases decision with omitted | ⟨emitted,info,z,a,source,clif,one,results,mapped⟩
  · exact stock_lower_omitted_scan_fall_refines run scope dominated events records
      block statement current recorded omitted
  · have classified := HighMulBody.emitted_record_family block statement current recorded emitted
      source clif one results mapped family
    exact stock_lower_mixed_highmul_record_fall_refines run scope dominated events records
      sourceFamily classified refines driver stable
end Backend.Stock.Proof.QuietSourceColors
#print axioms Backend.Stock.Proof.QuietSourceColors.highmul_source_record_fall_refines

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The final returned division is retained even after an arbitrary source
prefix. Its input is exactly the real return-request output, so retention does
not require a whole-body no-sinking certificate. -/
theorem stock_lower_last_div_return_emitted {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z]) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step),
      SourceBodySplit f event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart f event.block + front.length ∧ record.input = term.output.state ∧
      scanInstruction event.ctx event.block record.inst event.termInst event.isBranch record.input = .ok record.output ∧
      record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted := by
  obtain ⟨term,body,termStep,split,member,unsunk,branch,recorded,emitted⟩ :=
    stock_lower_retTrap_emitted run scope events block (by rw [ret]; rfl)
  have statement : b.body[front.length]? = some stm := by
    rw [shape,List.getElem?_append_right (Nat.le_refl _)]
    simp
  have defined : event.ctx.defInst? z = some (blockStart f event.block+front.length) :=
    stock_lower_source_result_definition run dominated events block statement (by simp [results])
  have safe := stock_lower_return_demand_unsunk run scope events block ret member
    split.termInst recorded emitted (by simp) defined
  have scanned := split.scanned
  simp only [sourceBodyIndices,shape,List.length_append,List.length_cons,List.length_nil,
    List.range_succ,List.map_append,List.map_cons,List.map_nil,List.reverse_append,
    List.reverse_cons,List.reverse_nil,List.nil_append,List.singleton_append] at scanned
  cases scanned with
  | cons head rest =>
    rename_i scan tail
    let record : ScanRecord := ⟨blockStart f event.block+front.length,term.output.state,scan⟩
    have current : record.inst = blockStart f event.block+front.length := rfl
    obtain ⟨info,source,clif,infoResults⟩ := ArithmeticBody.body_source_info run events split statement current
    have mandatory : event.ctx.insts[record.inst]!.clif.any mustLower = true := by
      simp only [getElem!_def,source,Option.getD_some,clif,division,Option.any,mustLower]
    have ordinary : record.inst ≠ event.termInst := by
      rw [current,split.termIndex,shape,List.length_append]
      simp only [List.length_cons,List.length_nil]
      omega
    obtain ⟨step,decision,actual⟩ := stock_mandatory_unsunk_emitted safe ordinary mandatory head
    exact ⟨term,record,_,step,split,List.mem_cons_self ..,rfl,rfl,head,
      split.retained record (List.mem_cons_self ..),decision,actual⟩
end Backend.Stock.Proof
#print axioms Backend.Stock.Proof.stock_lower_last_div_return_emitted
namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

set_option maxRecDepth 8192

/-- Extract the final division's actual retained record, result binding and
mapped virtual destination after an arbitrary original source prefix. -/
theorem actual_last_div_record {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z]) :
    ∃ (term record : ScanRecord) (body : BlockScan) (step : Step) (info : IInfo) (a : Nat),
      SourceBodySplit f event b term body ∧ record ∈ body.records ∧
      record.inst = blockStart f event.block+front.length ∧ record.input = term.output.state ∧
      record ∈ event.output.records ∧ record.output.step = some step ∧ step.decision = .emitted ∧
      event.ctx.insts[record.inst]? = some info ∧ info.clif = some (.div op ty x y) ∧
      info.results = [z] ∧ event.ctx.valueReg? z = some (.vreg a .int) := by
  obtain ⟨term,record,body,step,split,bodyMember,current,input,scan,member,recorded,emitted⟩ :=
    stock_lower_last_div_return_emitted run scope dominated events block shape division results ret
  have statement : b.body[front.length]? = some stm := by
    rw [shape,List.getElem?_append_right (Nat.le_refl _)]; simp
  obtain ⟨info,source,clif,infoResults⟩ := ArithmeticBody.body_source_info run events split statement current
  obtain ⟨emission,emissionRun,scanEq⟩ := stock_emitted_scan scan recorded emitted
  obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped (z := z) emissionRun
    (by simp only [getElem!_def,source,Option.getD_some,infoResults,results])
  have inv := (stock_lower_record_context run scope events).1
  obtain ⟨a,rfl⟩ := inv.valueReg z r mapped
  exact ⟨term,record,body,step,info,a,split,bodyMember,current,input,member,recorded,emitted,
    source,clif.trans (congrArg some division),infoResults.trans results,mapped⟩
end Backend.Stock.Proof.DivBody
#print axioms Backend.Stock.Proof.DivBody.actual_last_div_record
namespace Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- A retained record's source position occurs in the actual scan. -/
theorem ScansSpec.record_inst_mem {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (scanned : ScansSpec exec indices input output) {record : ScanRecord}
    (member : record ∈ output.records) : record.inst ∈ indices := by
  rw [← scanned.order]
  exact List.mem_map.mpr ⟨record,member,rfl⟩

/-- An actual scan of distinct source positions has one record per position.
This connects a derived retained division to any body-family classification at
that original index, without an externally chosen record identity. -/
theorem ScansSpec.record_unique {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (scanned : ScansSpec exec indices input output) (unique : indices.Nodup)
    {r s : ScanRecord} (first : r ∈ output.records) (second : s ∈ output.records)
    (same : r.inst = s.inst) : r = s := by
  induction scanned with
  | nil input => cases first
  | @cons i indices input scan tail head rest ih =>
    have fresh := List.nodup_cons.mp unique
    rcases List.mem_cons.mp first with rfl | first
    · rcases List.mem_cons.mp second with rfl | second
      · rfl
      · have member := rest.record_inst_mem second
        rw [← same] at member
        exact False.elim (fresh.1 member)
    · rcases List.mem_cons.mp second with rfl | second
      · have member := rest.record_inst_mem first
        rw [same] at member
        exact False.elim (fresh.1 member)
      · exact ih fresh.2 first second
end Backend.Stock.Proof
#print axioms Backend.Stock.Proof.ScansSpec.record_inst_mem
#print axioms Backend.Stock.Proof.ScansSpec.record_unique
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- Every real mixed-body record is either a previously proved scalar record
or a retained, bound division record. The actual driver derives these cases. -/
inductive MixedDivRecord (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop where
  | scalar {j : Nat} {b : Clif.Block} {stm : Clif.Stmt} {info : IInfo}
      (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
      (current : r.inst = blockStart f bi+j)
      (source : ctx.insts[r.inst]? = some info) (clif : info.clif = some stm.inst)
      (family : HighMulBody.Family stm.inst)
      (actual : PureBody.SourceRecord f ctx bi r) : MixedDivRecord f ctx bi r
  | division {j : Nat} {b : Clif.Block} {stm : Clif.Stmt} {step : Step} {info : IInfo}
      {op : Clif.DivOp} {ty : Clif.Ty} {x y z a : Nat}
      (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
      (current : r.inst = blockStart f bi+j)
      (source : ctx.insts[r.inst]? = some info) (clif : info.clif = some (.div op ty x y))
      (results : info.results = [z]) (statementResults : stm.results = [z])
      (mapped : ctx.valueReg? z = some (.vreg a .int))
      (recorded : r.output.step = some step) (emitted : step.decision = .emitted) :
      MixedDivRecord f ctx bi r

/-- Existing complete scalar handlers and the generic division handler compose
through one guarded original-source relation. -/
theorem MixedDivRecord.fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (classified : MixedDivRecord f event.ctx event.block record)
    (sourceFamily : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) record := by
  cases classified with
  | scalar block statement current source clif family actual =>
    exact QuietSourceColors.highmul_source_record_fall_refines run scope dominated events records
      block statement current family actual sourceFamily refines driver stable
  | division block statement current source clif results statementResults mapped recorded emitted =>
    exact stock_lower_div_scan_fall_refines run scope dominated events records
      block statement current _ source clif results statementResults mapped recorded emitted refines stable

/-- A real source trap is impossible at a pure prefix record; at a division,
the complete source bridge gives the real selected guard's coded halt. -/
theorem MixedDivRecord.trap_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {record : ScanRecord} (records : record ∈ event.output.records)
    (classified : MixedDivRecord f event.ctx event.block record)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    ScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) record := by
  cases classified with
  | @scalar j b stm info block statement current source clif family actual =>
    intro s code failed ρ w held
    obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
    have sameInfo : info' = info := Option.some.inj (found.symm.trans source)
    subst info'
    have sameInst : inst = stm.inst := Option.some.inj (original.symm.trans clif)
    subst inst
    rw [LocalBody.local_outcome (LocalBody.LocalInst.of_pure (HighMulBody.family_pure family))] at trapped
    exact False.elim (HighMulBody.highmul_inst_notrap family s.2.1 s.2.2 code trapped)
  | @division j b stm step info op ty x y z a block statement current source clif results statementResults mapped recorded emitted =>
    intro s code failed ρ w held
    obtain ⟨indexed,info',inst,rest,found,original,remaining,trapped⟩ := failed
    have sameInfo : info' = info := Option.some.inj (found.symm.trans source)
    subst info'
    have sameInst : inst = .div op ty x y := Option.some.inj (original.symm.trans clif)
    subst inst
    have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
    obtain ⟨func,dfg,memory,values⟩ := held
    rw [position] at dfg values
    obtain ⟨d,output,bounds,trap⟩ := ScalarDiv.stock_lower_div_source_trap run scope dominated events
      records block statement current source clif results mapped recorded emitted refines dfg values trapped
    exact trap w

end Backend.Stock.Proof
#print axioms Backend.Stock.Proof.MixedDivRecord.fall_refines
#print axioms Backend.Stock.Proof.MixedDivRecord.trap_refines

namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The real single-block event selects the source block, independently of
its instruction families and source outcomes. -/
private theorem mixed_event_block {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    f.blocks[event.block]? = some b := by
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split run scope events
  have bound := (List.getElem?_eq_some_iff.mp split.block).1
  rw [blocks] at bound
  have zero : event.block = 0 := by simpa using bound
  simp [zero,blocks]

/-- Derive every mixed body's actual record from its source syntax and real
whole-driver run. The final division's retention comes from return demand;
every pure prefix position derives quietness and its own concrete decision. -/
theorem actual_mixed_div_families {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records,MixedDivRecord f event.ctx event.block record := by
  have block := mixed_event_block run scope blocks events
  obtain ⟨term,last,body,step,info,a,split,lastMember,lastIndex,lastInput,
    lastRetained,lastStep,lastEmitted,lastSource,lastClif,lastResults,lastMapped⟩ :=
      actual_last_div_record run scope dominated events block shape division results ret
  have lastStatement : b.body[front.length]? = some stm := by
    rw [shape,List.getElem?_append_right (Nat.le_refl _)]; simp
  have unique : (sourceBodyIndices f event.block b).Nodup := by
    unfold sourceBodyIndices
    apply List.pairwise_reverse.mpr
    exact List.Pairwise.map (fun n => blockStart f event.block+n)
      (fun a b different eq => different (Nat.add_left_cancel eq.symm)) List.nodup_range
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,item,statement,current⟩ := split.positions record member
  by_cases final : j = front.length
  · subst j
    have same : record = last := split.scanned.record_unique unique member lastMember
      (current.trans lastIndex.symm)
    subst record
    have sameItem : item = stm := Option.some.inj (statement.symm.trans lastStatement)
    subst item
    exact .division block lastStatement lastIndex lastSource lastClif lastResults results
      lastMapped lastStep lastEmitted
  · have inside := (List.getElem?_eq_some_iff.mp statement).1
    have before : j < front.length := by
      rw [shape,List.length_append] at inside
      simp only [List.length_cons,List.length_nil] at inside
      omega
    have original : front[j]? = some item := by
      rw [shape,List.getElem?_append_left before] at statement
      exact statement
    have itemFamily := family item (List.mem_of_getElem? original)
    have described := QuietSourceColors.actual_quiet_source_record run scope blocks events split
      member statement current (HighMulBody.family_quiet itemFamily)
      (HighMulBody.family_single itemFamily f)
    obtain ⟨sourceInfo,source,clif,sourceResults⟩ := ArithmeticBody.body_source_info run events split statement current
    exact .scalar block statement current source clif itemFamily described

end Backend.Stock.Proof.DivBody
#print axioms Backend.Stock.Proof.DivBody.actual_mixed_div_families

namespace Backend.Stock.Proof.DivBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

private theorem mixed_memory_formats {f : Clif.Function} {b : Clif.Block}
    (blocks : f.blocks = [b]) {front : List Clif.Stmt} {stm : Clif.Stmt}
    (shape : b.body = front ++ [stm]) (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat} (division : stm.inst = .div op ty x y) :
    ∀ b' ∈ f.blocks,∀ item ∈ b'.body,CastComplete.MemoryFormat item.inst := by
  intro b' member item present
  have same : b' = b := by simpa only [blocks,List.mem_singleton] using member
  subst b'
  rw [shape] at present
  rcases List.mem_append.mp present with earlier | final
  · exact HighMulBody.family_formats (family item earlier)
  · have same : item = stm := by simpa only [List.mem_singleton] using final
    subst item
    rw [division]
    cases op <;> cases ty <;> simp [CastComplete.MemoryFormat,instNames]

private theorem mixed_local_family {b : Clif.Block} {front : List Clif.Stmt} {stm : Clif.Stmt}
    (shape : b.body = front ++ [stm]) (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y : Nat} (division : stm.inst = .div op ty x y) :
    ∀ item ∈ b.body,LocalBody.LocalInst item.inst := by
  intro item member
  rw [shape] at member
  rcases List.mem_append.mp member with earlier | final
  · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure (family item earlier))
  · have same : item = stm := by simpa only [List.mem_singleton] using final
    subst item
    simp [LocalBody.LocalInst,division]

/-- The complete real mixed body preserves successful source execution and
all original coded traps through one actual scan and one guarded relation. -/
theorem actual_mixed_div_body_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program} :
    ∃ term body,SourceBodySplit f event b term body ∧
      (∀ s s',SourceSteps (IndexedSourceInst env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s s' →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w → ∃ ρ' w',
          seqRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w =
            some (.fall ρ' w') ∧ GuardedScanRel f result event.ctx event.block MR term.output.state s' ρ' w') ∧
      (∀ s code,SourceTrapSteps (IndexedSourceInst env cp f event.ctx event.block)
        (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
        ((List.range b.body.length).map (blockStart f event.block+·)) s code →
        ∀ ρ w,GuardedScanRel f result event.ctx event.block MR event.output.state s ρ w →
          TrapRun isem (body.code.toList.map (·.mapRegs
            (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ w code) := by
  obtain ⟨term,body,split,classified⟩ := actual_mixed_div_families run scope dominated blocks
    shape family division results ret events
  have formats := mixed_memory_formats blocks shape family division
  have normal : ∀ r ∈ body.records,ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block)
      isem result.final.alias (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r member
    exact MixedDivRecord.fall_refines run scope dominated events
      (split.retained r member) (classified r member) formats refines driver stable
  have trapping : ∀ r ∈ body.records,ScanTrapRefines
      (LocalBody.IndexedSourceTrap env cp f event.ctx event.block) isem result.final.alias
      (GuardedScanRel f result event.ctx event.block MR) r := by
    intro r member
    exact MixedDivRecord.trap_refines run scope dominated events
      (split.retained r member) (classified r member) refines
  refine ⟨term,body,split,?_,?_⟩
  · intro s s' source ρ w held
    apply split.scanned.fall_refines normal s s'
    · simpa only [sourceBodyIndices,List.reverse_reverse] using source
    · simpa only [split.state] using held
  · intro s code source ρ w held
    apply split.scanned.trap_refines normal trapping s code
    · simpa only [sourceBodyIndices,List.reverse_reverse] using source
    · simpa only [split.state] using held

/-- Actual ABI entry and return for any proved scalar prefix followed by a
returned division, retaining arbitrary original values and original slots. -/
theorem actual_mixed_div_entry_return_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true) {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .returned vals mem)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,RunOkABI f result.code isem MR fr.slots ⟨0,0,ρ,w⟩ (.returned vals mem) := by
  apply PureBody.actual_local_entry_return_refines_frame run scope dominated abi blocks
    (mixed_local_family shape family division) ret entered returned refines driver memorySem stable
    (fun event events => ?_) memory arguments
  obtain ⟨term,body,split,normal,trapping⟩ := actual_mixed_div_body_refines run scope dominated blocks
    shape family division results ret events refines driver stable
  exact ⟨term,body,split,normal⟩

/-- Actual ABI entry and the original trapped source prefix reach the selected
real coded trap inside the complete mixed function. -/
theorem actual_mixed_div_entry_trap_refines_frame {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    {args : List Clif.Val} {cm : Clif.Mem} {fr : Clif.Frame} (entered : SourceEntry f args fr)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {code : Clif.TrapCode}
    (trapped : Clif.runLoop env cp fuel ⟨fr,[],cm⟩ = .trapped code)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    {w : Arm.ArmState} (memory : MR fr.slots cm w) (arguments : ArgsAtEntry F f.sig args w) :
    ∃ ρ,VTrapFrom result.code isem ⟨0,0,ρ,w⟩ code := by
  apply LocalBody.actual_local_entry_trap_refines_frame run scope dominated blocks
    (mixed_local_family shape family division) ret entered trapped refines driver memorySem stable
    (fun event events => ?_) memory arguments
  obtain ⟨term,body,split,normal,trapping⟩ := actual_mixed_div_body_refines run scope dominated blocks
    shape family division results ret events refines driver stable
  exact ⟨term,body,split,trapping⟩

end Backend.Stock.Proof.DivBody
#print axioms Backend.Stock.Proof.DivBody.actual_mixed_div_body_refines
#print axioms Backend.Stock.Proof.DivBody.actual_mixed_div_entry_return_refines_frame
#print axioms Backend.Stock.Proof.DivBody.actual_mixed_div_entry_trap_refines_frame

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false

/-- The existing full return-and-trap contract for any proved scalar prefix
followed by a returned division. Original arguments, memory and slots remain
arbitrary; compiler records and binding facts are derived internally. -/
theorem domain_of_mixed_div {f : Clif.Function}
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true)
    {b : Clif.Block} (blocks : f.blocks = [b])
    {front : List Clif.Stmt} {stm : Clif.Stmt} (shape : b.body = front ++ [stm])
    (family : ∀ item ∈ front,HighMulBody.Family item.inst)
    {op : Clif.DivOp} {ty : Clif.Ty} {x y z : Nat}
    (division : stm.inst = .div op ty x y) (results : stm.results = [z])
    (ret : b.term = .ret [z])
    (ordinary : (sigRets f.sig).any (·.purpose == .sret) = false) : Domain f := by
  refine ⟨scope,dominated,abi,ordinary,?_,?_⟩
  · intro result run args cm fr entered env cp fuel vals mem returned F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact DivBody.actual_mixed_div_entry_return_refines_frame run scope dominated abi blocks
      shape family division results ret entered returned refines driver memorySem stable memory arguments
  · intro result run args cm fr entered env cp fuel code trapped F isem refines driver
      sb syms memorySem MR stable w memory arguments
    exact DivBody.actual_mixed_div_entry_trap_refines_frame run scope dominated blocks
      shape family division results ret entered trapped refines driver memorySem stable memory arguments

end Backend.Stock.Scalar
#print axioms Backend.Stock.Scalar.domain_of_mixed_div

namespace Backend.Stock.Scalar
set_option autoImplicit false
set_option Elab.async false

/-- Previously proved scalar syntax before one final returned division.
The old single-division and pure-body classifiers remain unchanged. -/
def mixedDivEligible (b : Clif.Block) : Bool :=
  match b.body.reverse,b.term with
  | ⟨[z],.div _ ty _ _⟩ :: front,.ret [z'] =>
      z == z' && (ty == .i32 || ty == .i64) && front.all highmulBodyEligible
  | _,_ => false

/-- The classifier derives source shape and every prefix family internally. -/
theorem mixedDivEligible_sound {b : Clif.Block} (checked : mixedDivEligible b = true) :
    ∃ (front : List Clif.Stmt) (stm : Clif.Stmt) (op : Clif.DivOp) (ty : Clif.Ty) (x y z : Nat),
      b.body = front ++ [stm] ∧
      (∀ item ∈ front,Proof.HighMulBody.Family item.inst) ∧
      stm.inst = .div op ty x y ∧ stm.results = [z] ∧ b.term = .ret [z] := by
  unfold mixedDivEligible at checked
  split at checked
  next z op ty x y front z' body ret =>
    simp only [Bool.and_eq_true] at checked
    have equal : z = z' := beq_iff_eq.mp checked.1.1
    subst z'
    refine ⟨front.reverse,⟨[z],.div op ty x y⟩,op,ty,x,y,z,?_,?_,rfl,rfl,ret⟩
    · have reversed := congrArg List.reverse body
      simpa only [List.reverse_reverse,List.reverse_cons,List.reverse_nil,List.nil_append] using reversed
    · intro item member
      exact highmulBodyEligible_sound (List.all_eq_true.mp checked.2 item (List.mem_reverse.mp member))
  next => cases checked
end Backend.Stock.Scalar
#print axioms Backend.Stock.Scalar.mixedDivEligible_sound
