import FV.Backend.Proof.StockScanSemantics
import FV.Backend.Proof.IselCmpDiv

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

private theorem local_outcome {env : Clif.Env} {cp : Clif.Program}
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
      exact evaluated
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
          have source := actual_local_source_step run events split
            (record := ⟨blockStart f event.block+j,default,default⟩) statement rfl instFamily head next
          have tail := ih (s := t) (j := j+1) (by omega) rfl callers ret trapped
          have prefixStep := SourceTrapSteps.next source tail
          simpa only [Nat.add_assoc,Nat.add_comm 1 j] using prefixStep

end Backend.Stock.Proof.LocalBody
#print axioms Backend.Stock.Proof.LocalBody.actual_local_source_trap
#print axioms Backend.Stock.Proof.LocalBody.actual_local_source_trap_execution
