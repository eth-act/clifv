import FV.Backend.Proof.StockCmpParameterDriverRuns
import FV.Backend.Proof.StockCmpParameterSourceValues
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.ScalarCmp.ParameterDriverWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
private abbrev function := cmpParameterFunction
private abbrev built := cmpParameterBuilt
private abbrev sourceKey := cmpSourceKey
private abbrev ctxKey := cmpCtxKey
private abbrev observed := stock_cmp_parameter_driver_observed
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frame (trapping : Bool) : Clif.Frame := {
  func := function
  regs := fun x => if x = 7 then some (.ofInt .i64 7) else
    if x = 31 then some (.ofInt .i64 (if trapping then 0 else 3)) else none
  slots := [],body := [⟨[100],.icmp .eq .i64 7 31⟩],term := .ret [100] }
private def regs (trapping : Bool) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+(BitVec.ofNat 64 7).toNat)
  else if n = 193 then BitVec.ofNat 128 (2^100+(if trapping then 0 else 3)) else 0
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem dfg_base (trapping : Bool) : DFGCons (built).1 (frame trapping) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : (built).1.defInst? 7 = none := by rfl
      rw [absent] at defined; cases defined
    · by_cases thirtyone : x = 31
      · subst x
        have absent : (built).1.defInst? 31 = none := by rfl
        rw [absent] at defined; cases defined
      · simp [frame,seven,thirtyone] at lookup
  · intro x t v typed lookup
    by_cases present : x = 7 ∨ x = 31
    · rcases present with rfl | rfl
      all_goals change some (.int _) = some t at typed
      all_goals cases typed; cases lookup; rfl
    · simp only [not_or] at present
      simp [frame,present.1,present.2] at lookup
private theorem dfg_transport {a b : Ctx} {fr : Clif.Frame}
    (insts : a.insts.map sourceKey = b.insts.map sourceKey)
    (types : a.valTy = b.valTy) (defs : a.valDef = b.valDef) (dfg : DFGCons b fr) : DFGCons a fr := by
  constructor
  · intro x j info cl v defined found original pure lookup
    have view : (b.insts[j]?).map sourceKey = some (sourceKey info) := by
      rw [← Array.getElem?_map,← insts,Array.getElem?_map,found]; rfl
    obtain ⟨info',found',same⟩ := Option.map_eq_some_iff.mp view
    have clifEq := congrArg Prod.fst same
    have resultsEq := congrArg Prod.snd same
    change info'.clif = info.clif at clifEq
    change info'.results = info.results at resultsEq
    obtain ⟨vals,evaluated,written⟩ := dfg.1 x j info' cl v
      (by simpa only [Ctx.defInst?,defs] using defined) found' (clifEq.trans original) pure lookup
    exact ⟨vals,evaluated,by rw [← resultsEq]; exact written⟩
  · simpa only [FrameTyped,Ctx.valueType?,types] using dfg.2
private structure Inputs (trapping : Bool) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = (0 : Nat)
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.icmp .eq .i64 7 31)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int)
  typeX : event.ctx.valueType? 7 = some (.int 64)
  typeY : event.ctx.valueType? 31 = some (.int 64)
  parameterX : event.ctx.defInst? 7 = none
  parameterY : event.ctx.defInst? 31 = none
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some rule_lower_2215.id
  dfg : DFGCons event.ctx (frame trapping)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame trapping)
    (fun k => regs trapping (aliasNum result.final.alias k))

private theorem inputs (trapping : Bool) :
    Nonempty (Inputs trapping) := by
  have actual := observed
  cases run : Stock.lower (function) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,stepData⟩ := actual
    simp only [ctxKey,cmpCtxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some rule_lower_2215.id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.icmp .eq .i64 7 31),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.icmp .eq .i64 7 31) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int) := by
      simp only [Ctx.valueReg?,maps]
      rfl
    have typeX : event.ctx.valueType? 7 = some (.int 64) := by simp only [Ctx.valueType?,types]; rfl
    have typeY : event.ctx.valueType? 31 = some (.int 64) := by simp only [Ctx.valueType?,types]; rfl
    have parameterX : event.ctx.defInst? 7 = none := by simp only [Ctx.defInst?,defs]; rfl
    have parameterY : event.ctx.defInst? 31 = none := by simp only [Ctx.defInst?,defs]; rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame trapping)
        (fun n => regs trapping (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt .i64 7) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rfl
        · dsimp only
          rw [alias192]
          cases trapping <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          change some (.ofInt .i64 (if trapping then 0 else 3)) = some val at lookup
          cases lookup
          refine ⟨193,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            rfl
          · dsimp only
            rw [alias193]
            cases trapping <;> unfold VHolds <;> decide +kernel
        · simp [frame,seven,thirtyone] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,typeX,typeY,parameterX,parameterY,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base trapping),held⟩⟩

private theorem dominated : Dominated function := by
  constructor
  · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function,cmpParameterFunction] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        change y ∈ [7,31] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> simp [availOf,function,cmpParameterFunction,defsBefore,defsFrom]
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        simp [availOf,function,cmpParameterFunction,defsBefore,defsFrom]
    | succ bi => simp [function,cmpParameterFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 1 := rfl
    omega
private theorem frame_available (trapping : Bool) (ctx : Ctx) :
    (restrict (frame trapping) (availOf function (availIn function ctx) 0 0)).regs = (frame trapping).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,cmpParameterFunction,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]
private theorem restrictedDFG (trapping : Bool) (input : Inputs trapping) :
    DFGCons input.event.ctx (restrict (frame trapping) (availOf function (availIn function input.result.ctx) 0 0)) :=
  dfgCons_congr (ctx := input.event.ctx) (fr := frame trapping) rfl rfl (frame_available trapping input.result.ctx) input.dfg
private theorem getX (trapping : Bool) (ctx : Ctx) :
    (restrict (frame trapping) (availOf function (availIn function ctx) 0 0)).getAs 7 .i64 = .ok (BitVec.ofNat 64 7) := by
  have same := getAs_congr (fr := frame trapping)
    (fr' := restrict (frame trapping) (availOf function (availIn function ctx) 0 0))
    (x := 7) (ty := .i64) (congrFun (frame_available trapping ctx) 7)
  exact same.trans rfl
private theorem getY (trapping : Bool) (ctx : Ctx) :
    (restrict (frame trapping) (availOf function (availIn function ctx) 0 0)).getAs 31 .i64 =
      .ok (BitVec.ofNat 64 (if trapping then 0 else 3)) := by
  have same := getAs_congr (fr := frame trapping)
    (fr' := restrict (frame trapping) (availOf function (availIn function ctx) 0 0))
    (x := 31) (ty := .i64) (congrFun (frame_available trapping ctx) 31)
  cases trapping <;> exact same.trans rfl
private theorem current (trapping : Bool) (input : Inputs trapping) :
    input.record.inst = blockStart function 0 + (0 : Nat) := by
  simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
private theorem guarded (trapping : Bool) (input : Inputs trapping) :
    ValuesHeld (fun v => Demanded input.record.output.state v ∧ v ∈ availOf function (availIn function input.result.ctx) 0 0)
      input.event.ctx (frame trapping) (fun key => regs trapping (aliasNum input.result.final.alias key)) :=
  input.held.mono (fun _ needed => needed.1)
/-- A complete actual retained Stock.lower comparison and original source step
inhabit fresh result binding, original guarded source transfer and boolean
execution, with dirty upper input bits and sparse original source numbering. -/
theorem stock_cmp_parameter_complete_source_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_2215.id ∧
      step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame false,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs false) world (fun ρ' _ =>
          VHolds ⟨.i8,0#8⟩ (ρ' d) ∧ (∀ k,k ≠ d → ρ' k = regs false k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf function (availIn function result.ctx) 0 1) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs false
  let value : Clif.Val := ⟨.i8,0#8⟩
  let fr' : Clif.Frame := {frame false with regs := (frame false).regs.set 100 value,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame false) Clif.Mem.empty (.icmp .eq .i64 7 31) =
      .ok ([value],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame false,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.icmp .eq .i64 7 31,[value],(frame false).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    · rw [input.results]; rfl
    · rw [input.results]; rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_cmp_parameter_source_values input.run scope dominated input.events input.records
    (bi := 0) (j := 0) (block := function.blocks[0]!) rfl rfl (current false input) input.source input.clif (by decide)
    input.typeX input.typeY input.parameterX input.parameterY input.results rfl input.mapped input.recorded input.emitted
    self (restrictedDFG false input) (getX false input.result.ctx) (getY false input.result.ctx) (guarded false input) sourceStep
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,scope,dominated,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,lower,upper,sourceStep,execution⟩
end Backend.Stock.Proof.ScalarCmp.ParameterDriverWitness
