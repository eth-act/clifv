import FV.Backend.Proof.StockReturnFullBody
import FV.Backend.Proof.StockReturnRecordSource
import FV.Backend.Proof.StockReturnDriverRuns
import FV.Backend.Proof.StockReturnContract
import FV.Backend.Proof.StockMemoryNopBody
import FV.Backend.Proof.StockEntrySeed

namespace Backend.Stock.Proof.ReturnFullBodyWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64 ReturnFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
private def args (p : Case) (a b : BitVec p.ty.width) : List Clif.Val :=
  if p.sret then [⟨p.ty,a⟩] else [⟨p.ty,a⟩,⟨p.ty,b⟩]
private def values (p : Case) (a b : BitVec p.ty.width) : List Clif.Val :=
  if p.sret then [] else [⟨p.ty,a⟩,⟨p.ty,b⟩]
private def frame (p : Case) (a b : BitVec p.ty.width) : Clif.Frame := {
  func := function p,slots := [],body := [],term := .ret (explicitXs p)
  regs := if p.sret then Clif.Regs.empty.set 7 ⟨p.ty,a⟩
    else (Clif.Regs.empty.set 7 ⟨p.ty,a⟩).set 31 ⟨p.ty,b⟩ }
private theorem requests (p : Case) : explicitXs p ++ sretRet (function p) = abiXs p := by
  cases flag : p.sret <;> simp [explicitXs,abiXs,sretRet,sigRets,function,flag]
private theorem scope (p : Case) : LowerScope (function p) := by
  apply lowerScope_of
  rcases p with ⟨sret,ty,width,pointer,int⟩
  cases sret with
  | true => have same := pointer rfl; subst ty; rfl
  | false => cases ty <;> simp [Clif.Ty.width] at width int <;> rfl
private theorem abi (p : Case) : sigAbiOk (function p).sig = true := by
  rcases p with ⟨sret,ty,width,pointer⟩
  cases sret with
  | true => have same := pointer rfl; subst ty; rfl
  | false => rfl
private theorem dominated (p : Case) : Dominated (function p) := by
  constructor
  · cases flag : p.sret <;> simp [valueDefs,function,flag] <;> decide +kernel
  · intro ctx ranges st build bi b found
    cases bi with
    | zero =>
      simp [function] at found
      subst b
      constructor
      · intro j stm statement; simp at statement
      · intro x member
        have request : x ∈ abiXs p := by
          simpa only [abiTerm,Driver.termArgs,requests p] using member
        cases flag : p.sret
        · simp only [abiXs,flag,Bool.false_eq_true,ite_false,List.mem_cons,List.not_mem_nil,or_false] at request
          rcases request with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom,flag]
        · simp only [abiXs,flag,ite_true,List.mem_singleton] at request
          subst x
          simp [availOf,function,defsBefore,defsFrom,flag]
    | succ bi => simp [function] at found
  · intro ctx ranges st build tl x incoming notLocal y member
    have bound := (inFix_fixOk (f := function p) (ctx := ctx) (gn := id)).cand tl x incoming
    have length : (function p).blocks.length = 1 := rfl
    omega
private theorem entered (p : Case) (a b : BitVec p.ty.width) :
    Clif.enterFunc (function p) (args p a b) Clif.Mem.empty = .ok (frame p a b,Clif.Mem.empty) := by
  cases flag : p.sret <;>
    simp [Clif.enterFunc,Clif.checkTys,Clif.AbiParam.tys,Clif.Function.entry?,function,args,frame,explicitXs,
      flag,Clif.enterSlots,Clif.bumpSlots,Clif.Regs.setMany,Clif.Res.ofOption,Clif.Res.check]
  all_goals exact ⟨rfl,rfl⟩
private theorem returned (p : Case) (a b : BitVec p.ty.width) :
    Clif.stepTerm Clif.Env.empty {funcs := []} ⟨frame p a b,[],Clif.Mem.empty⟩ (.ret (explicitXs p)) =
      .done (values p a b) Clif.Mem.empty := by
  cases flag : p.sret <;>
    simp [Clif.stepTerm,Clif.StepResult.ofRes,Clif.returnValues,Clif.checkTys,Clif.AbiParam.tys,
      Clif.Frame.getMany,Clif.Frame.get,Clif.Regs.set,Clif.Regs.empty,function,frame,explicitXs,values,flag,Clif.Res.ofOption,Clif.Res.check]
  all_goals rfl
private structure Inputs (p : Case) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  step : Step
  run : Stock.lower (function p) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  block : event.block = 0
  current : record.inst = 0
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  code : record.output.emitted = #[.rets ((registers p).zip (pins p))]
  state : record.output.state = afterReturn p (scanState record.input record.inst)
  map7 : event.ctx.valueReg? 7 = some (.vreg 192 .int)
  def7 : event.ctx.defInst? 7 = none
  normal : p.sret = false → event.ctx.valueReg? 31 = some (.vreg 193 .int) ∧ event.ctx.defInst? 31 = none
  alias7 : aliasNum result.final.alias 192 = 192
  alias31 : aliasNum result.final.alias 193 = 193
private theorem inputs (p : Case) : Nonempty (Inputs p) := by
  have actual := stock_return_driver_observed p
  unfold Observed at actual
  cases run : Stock.lower (function p) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq,
      List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias7,alias31,event,events,block,map7,def7,normal,record,records,current,stepData,code,state⟩ := actual
    obtain ⟨step,recorded,emitted⟩ := (by simpa only [Option.any_eq_true,beq_iff_eq] using stepData :
      ∃ step,record.output.step = some step ∧ step.decision = .emitted)
    have ordinary : p.sret = false → event.ctx.valueReg? 31 = some (.vreg 193 .int) ∧ event.ctx.defInst? 31 = none := by
      intro flag
      simpa only [flag,Bool.false_eq_true,ite_false,decide_eq_true_eq] using normal
    exact ⟨⟨result,event,record,step,run,events,records,block,current,recorded,emitted,code,state,map7,def7,ordinary,alias7,alias31⟩⟩
private def ContractPlacement (p : Case) : Prop :=
  (Stock.lower (function p)).toOption.map (fun result => decide
    (0 < result.code.blocks.size ∧ (result.code.blocks[0]!).insts =
      #[.args ((registers p).zip (pins p)),.rets ((registers p).zip (pins p))])) = some true
section ContractKernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem contract8 : ContractPlacement ⟨false,.i8,by simp [Clif.Ty.width],by simp,rfl⟩ := by
  unfold ContractPlacement; native_decide
private theorem contract16 : ContractPlacement ⟨false,.i16,by simp [Clif.Ty.width],by simp,rfl⟩ := by
  unfold ContractPlacement; native_decide
private theorem contract32 : ContractPlacement ⟨false,.i32,by simp [Clif.Ty.width],by simp,rfl⟩ := by
  unfold ContractPlacement; native_decide
private theorem contract64 : ContractPlacement ⟨false,.i64,by simp [Clif.Ty.width],by simp,rfl⟩ := by
  unfold ContractPlacement; native_decide
private theorem contractPointer : ContractPlacement ⟨true,.i64,by simp [Clif.Ty.width],fun _ => rfl,rfl⟩ := by
  unfold ContractPlacement; native_decide
end ContractKernel
private theorem contractPlacement (p : Case) : ContractPlacement p := by
  rcases p with ⟨sret,ty,width,pointer,int⟩
  cases sret with
  | true => have same := pointer rfl; subst ty; exact contractPointer
  | false =>
    cases ty
    all_goals first
      | exact contract8
      | exact contract16
      | exact contract32
      | exact contract64
      | (simp [Clif.Ty.width] at width; done)
      | (simp at int; done)

private theorem nil_source_points {S : Type} {step : Nat → S → S → Prop} {s t : S}
    (steps : SourceSteps step [] s t) : s = t := by cases steps; rfl

theorem stock_return_full_body_witness (p : Case) (a b : BitVec p.ty.width) :
    ∃ result : Result, Stock.lower (function p) = .ok result ∧
      ∀ world,∃ t : Clif.State, t.frame.regs = (frame p a b).regs ∧
        ReturnValuesAt (function p) result.code result.edgeArgs ispec (fun _ _ _ => True)
          t ⟨0,1,entrySeed result.ctx (frame p a b),world⟩
          (explicitXs p) (values p a b) Clif.Mem.empty := by
  obtain ⟨input⟩ := inputs p
  have block : (function p).blocks[input.event.block]? = some (function p).blocks[0]! := by rw [input.block]; rfl
  have sourceDefined : SourceDefinedAt (function p) input.result.ctx input.event.block 0 (frame p a b) := by
    rw [input.block]
    exact source_defined_enterFunc (dominated p) input.result.ctx (entered p a b)
  have observed := contractPlacement p
  unfold ContractPlacement at observed
  rw [input.run] at observed
  simp only [Except.toOption,Option.map_some,Option.some.injEq,decide_eq_true_eq] at observed
  obtain ⟨bound,code⟩ := observed
  have placed : input.result.code.blocks[0]? = some input.result.code.blocks[0]! := by simp [bound]
  have resolve7 : Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1)
      (.vreg 192 .int) = .vreg 192 .int := by
    rw [resolve_vreg]
    change Reg.vreg (aliasNum input.result.final.alias 192) .int = _
    rw [input.alias7]
  have resolve31 : Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1)
      (.vreg 193 .int) = .vreg 193 .int := by
    rw [resolve_vreg]
    change Reg.vreg (aliasNum input.result.final.alias 193) .int = _
    rw [input.alias31]
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ _ _ => True) := by intro _ _ _ _ _ h; exact h
  obtain ⟨termRecord,body,splitting,bodyRun⟩ := Backend.Stock.Memory.stock_nop_body
    input.run (scope p) (dominated p) input.events block (by intro stm impossible; cases impossible)
    (isem := ispec) (MR := fun _ _ _ => True) (env := Clif.Env.empty) (cp := {funcs := []})
  have nilScan : ScansSpec (fun i => scanInstruction input.event.ctx input.event.block i input.event.termInst input.event.isBranch) [] termRecord.output.state body := by
    have indices : sourceBodyIndices (function p) input.event.block (function p).blocks[0]! = [] := rfl
    simpa only [indices] using splitting.scanned
  have empty : body.code = #[] ∧ body.records = [] := by cases nilScan; exact ⟨rfl,rfl⟩
  have sameRecord : input.record = termRecord := by
    have member := input.records
    rw [splitting.records,empty.2] at member
    exact List.mem_singleton.mp member
  have eventCode : input.event.output.code = input.record.output.emitted := by
    rw [splitting.code,empty.1,Array.empty_append,sameRecord]
  have pieces : input.result.code.blocks[0]!.insts =
      #[.args ((registers p).zip (pins p))] ++ input.event.output.code.map
        (·.mapRegs (Backend.lowerFunction.resolve input.result.final.alias (input.result.final.alias.size+1))) ++ #[] := by
    rw [code,eventCode,input.code]
    cases flag : p.sret <;> simp [registers,pins,flag,MInst.mapRegs,resolve7,resolve31]
  have sourceReturned : Clif.runLoop Clif.Env.empty {funcs := []} 1
      ⟨frame p a b,[],Clif.Mem.empty⟩ = .returned (values p a b) Clif.Mem.empty := by
    rw [Clif.runLoop_succ,Clif.step_term _ _ _ (show (frame p a b).body = [] from rfl)]
    change (match Clif.stepTerm Clif.Env.empty {funcs := []} ⟨frame p a b,[],Clif.Mem.empty⟩ (.ret (explicitXs p)) with
      | .next t => Clif.runLoop Clif.Env.empty {funcs := []} 0 t
      | .done vals mem => .returned vals mem
      | .trapped c => .trapped c
      | .stuck message => .stuck message) = _
    rw [returned p a b]
  refine ⟨input.result,input.run,?_⟩
  intro world
  have initial := stock_lower_entered_seed_guarded_frame input.run (scope p) (dominated p)
    input.events (SourceEntry.of_enterFunc (entered p a b)) input.event.output.state
    (MR := fun _ _ _ => True) (cm := Clif.Mem.empty) world trivial
  obtain ⟨t,steps,slots,unchanged,full⟩ := OrdinaryBody.actual_ordinary_return_full_values_at_block
    input.run (scope p) (dominated p) (abi p)
    (by intro stm impossible; cases impossible) rfl input.events splitting
    rfl rfl rfl rfl sourceDefined sourceReturned self stable bodyRun placed pieces _ world initial
  have trace : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} (function p)
      input.event.ctx input.event.block) []
      (0,frame p a b,Clif.Mem.empty) (0,t.frame,t.mem) := by simpa [function] using steps
  have sameRegs : t.frame.regs = (frame p a b).regs := by
    exact congrArg (fun point : SourcePoint => point.2.1.regs) (nil_source_points trace).symm
  have seed : entrySeed input.event.ctx (frame p a b) = entrySeed input.result.ctx (frame p a b) := by
    have maps := funext (stock_lower_record_context input.run (scope p) input.events).2.1
    unfold entrySeed
    rw [maps]
  exact ⟨t,sameRegs,by simpa only [Array.size_singleton,seed] using full⟩

end Backend.Stock.Proof.ReturnFullBodyWitness
