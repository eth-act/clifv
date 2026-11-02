import FV.Backend.Proof.StockReturnFullValues
import FV.Backend.Proof.StockReturnRecordSource
import FV.Backend.Proof.StockReturnDriverRuns
import FV.Backend.Proof.StockReturnContract

namespace Backend.Stock.Proof.ReturnFullValuesWitness
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
private def machine (p : Case) (a b : BitVec p.ty.width) (key : Nat) : CV :=
  BitVec.ofNat 128 (2^100 + if key = 192 then a.toNat else b.toNat)
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
private theorem dirty (p : Case) (word : BitVec p.ty.width) :
    (BitVec.ofNat 128 (2^100+word.toNat)).setWidth p.ty.width = word := by
  have bound : p.ty.width ≤ 128 := by rcases p.width with h | h | h | h <;> omega
  have high : 2^100 % 2^p.ty.width = 0 := by rcases p.width with h | h | h | h <;> rw [h] <;> decide +kernel
  rw [BitVec.setWidth_ofNat_of_le bound]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.add_mod,high,Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
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
private theorem request_map (p : Case) (input : Inputs p) :
    (abiXs p).mapM input.event.ctx.valueReg? = some (registers p) := by
  cases flag : p.sret
  · have normal := (input.normal flag).1
    simp [abiXs,registers,flag,input.map7,normal]
  · simp [abiXs,registers,flag,input.map7]
private theorem safe (p : Case) (input : Inputs p) (st : State) :
    ∀ x ∈ abiXs p,DemandAllowed input.event.ctx st x := by
  intro x member i defined
  cases flag : p.sret
  · simp only [abiXs,flag,Bool.false_eq_true,ite_false,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · rw [input.def7] at defined; cases defined
    · rw [(input.normal flag).2] at defined; cases defined
  · simp only [abiXs,flag,ite_true,List.mem_singleton] at member
    subst x
    rw [input.def7] at defined; cases defined
private theorem selected_pins (p : Case) : returnPins (function p) (registers p).length = some (pins p) := by
  cases flag : p.sret <;> simp [returnPins,function,registers,pins,sigRets,retRegs,flag]
  all_goals rfl
private theorem held (p : Case) (input : Inputs p) (a b : BitVec p.ty.width) :
    ValuesHeld (fun x => x ∈ explicitXs p ++ sretRet (function p)) input.event.ctx (frame p a b)
      (fun key => machine p a b (aliasNum input.result.final.alias key)) := by
  intro x member value lookup
  rw [requests] at member
  cases flag : p.sret
  · simp only [abiXs,flag,Bool.false_eq_true,ite_false,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · simp [frame,flag,Clif.Regs.set,Clif.Regs.empty] at lookup
      subst value
      refine ⟨192,input.map7,?_⟩
      dsimp only
      rw [input.alias7]
      exact dirty p a
    · simp [frame,flag,Clif.Regs.set,Clif.Regs.empty] at lookup
      subst value
      refine ⟨193,(input.normal flag).1,?_⟩
      dsimp only
      rw [input.alias31]
      exact dirty p b
  · simp only [abiXs,flag,ite_true,List.mem_singleton] at member
    subst x
    simp [frame,flag,Clif.Regs.set,Clif.Regs.empty] at lookup
    subst value
    refine ⟨192,input.map7,?_⟩
    dsimp only
    rw [input.alias7]
    exact dirty p a

theorem stock_return_full_values_witness (p : Case) (a b : BitVec p.ty.width) :
    ∃ result : Result, Stock.lower (function p) = .ok result ∧ LowerScope (function p) ∧
      Dominated (function p) ∧ sigAbiOk (function p).sig = true ∧
      Clif.enterFunc (function p) (args p a b) Clif.Mem.empty = .ok (frame p a b,Clif.Mem.empty) ∧
      Clif.stepTerm Clif.Env.empty {funcs := []} ⟨frame p a b,[],Clif.Mem.empty⟩ (.ret (explicitXs p)) =
        .done (values p a b) Clif.Mem.empty ∧
      ∀ world,∃ label k, ReturnValuesAt (function p) result.code result.edgeArgs ispec (fun _ _ _ => True)
        ⟨frame p a b,[],Clif.Mem.empty⟩ ⟨label,k,machine p a b,world⟩
        (explicitXs p) (values p a b) Clif.Mem.empty := by
  obtain ⟨input⟩ := inputs p
  have block : (function p).blocks[input.event.block]? = some (function p).blocks[0]! := by rw [input.block]; rfl
  obtain ⟨original,term,body,split⟩ := stock_lower_body_scan_split input.run (scope p) input.events
  have same := Option.some.inj (split.block.symm.trans block)
  subst original
  have terminal : input.record.inst = input.event.termInst := by
    rw [input.current,split.termIndex,input.block]; rfl
  have guarded : ValuesHeld (fun x => Demanded input.record.output.state x ∧
      x ∈ availOf (function p) (availIn (function p) input.result.ctx) input.event.block 0)
      input.event.ctx (frame p a b) (fun key => machine p a b (aliasNum input.result.final.alias key)) := by
    intro x available
    apply held p input a b x
    rw [requests p]
    have availability := available.2
    rw [input.block] at availability
    have entry : (function p).blocks[0]? = some (function p).blocks[0]! := rfl
    obtain ⟨present,_⟩ := (mem_av entry).mp availability
    rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
    · cases flag : p.sret <;> simpa [function,abiXs,flag] using parameter
    · have bound := (inFix_fixOk (f := function p) (ctx := input.result.ctx) (gn := id)).cand 0 x incoming
      omega
    · omega
  have sourceDefined : SourceDefinedAt (function p) input.result.ctx input.event.block 0 (frame p a b) := by
    rw [input.block]
    exact source_defined_enterFunc (dominated p) input.result.ctx (entered p a b)
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ _ _ => True) := by intro _ _ _ _ _ h; exact h
  refine ⟨input.result,input.run,scope p,dominated p,abi p,entered p a b,returned p a b,?_⟩
  intro world
  obtain ⟨label,blockCode,k,placed,segment⟩ := stock_lower_record_segment input.run input.events input.records
  refine ⟨label,k,?_⟩
  exact stock_lower_return_record_full_values input.run (scope p) (dominated p) (abi p)
    input.events block rfl input.records terminal rfl rfl (returned p a b) sourceDefined guarded self stable placed segment world trivial


/-- An arbitrary sret pointer survives in the actual implicit x8 return operand. -/
theorem stock_sret_x8_value_witness (word : BitVec 64) :
    let p : Case := ⟨true,.i64,by simp [Clif.Ty.width],fun _ => rfl,rfl⟩
    ∃ result : Result, Stock.lower (function p) = .ok result ∧
      ∀ world,∃ label k source value finalWorld,
        PerEdgePrep.VRetFromAt result.code result.edgeArgs ispec
          ⟨label,k,machine p word word,world⟩ [(source,.x 8)] [value] finalWorld ∧
        VHolds (⟨.i64,word⟩ : Clif.Val) value := by
  let p : Case := ⟨true,.i64,by simp [Clif.Ty.width],fun _ => rfl,rfl⟩
  obtain ⟨result,run,_,_,_,_,_,observed⟩ := stock_return_full_values_witness p word word
  refine ⟨result,run,?_⟩
  intro world
  obtain ⟨label,k,returned⟩ := observed world
  have pointer : (frame p word word).getMany (explicitXs p ++ sretRet (function p)) =
      .ok [(⟨.i64,word⟩ : Clif.Val)] := by rw [requests]; rfl
  obtain ⟨source,value,finalWorld,execution,held,_,_⟩ := returned.sret_value (by rfl) pointer
  exact ⟨label,k,source,value,finalWorld,execution,held⟩

end Backend.Stock.Proof.ReturnFullValuesWitness
