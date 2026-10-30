import FV.Backend.Proof.StockMinMaxRegisterDriverRuns
import FV.Backend.Proof.StockMinMaxRegisterSourceReads
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.ScalarSelect.MinMaxDriverWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarSelect Backend.Stock.Proof.ScalarSelect.MinMaxRegisterFixture
open Backend.Stock.Proof.ScalarCmp
private abbrev function := minmaxFunction
private abbrev built := minmaxBuilt
private abbrev sourceKey := minmaxSourceKey
private abbrev ctxKey := minmaxCtxKey
private abbrev observed := stock_minmax_register_driver_observed
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frame (unsigned maximum : Bool) : Clif.Frame := {
  func := (function unsigned maximum)
  regs := fun x => if x = 7 then some (.ofInt .i64 (-7)) else
    if x = 31 then some (.ofInt .i64 9) else none
  slots := [],body := [⟨[100],.binary (minmaxOperation unsigned maximum) .i64 7 31⟩],term := .ret [100] }
private def regs (unsigned maximum : Bool) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+(BitVec.ofInt 64 (-7)).toNat)
  else if n = 193 then BitVec.ofNat 128 (2^100+9) else 0
private theorem scope (unsigned maximum : Bool) : LowerScope (function unsigned maximum) := lowerScope_of (by cases unsigned <;> cases maximum <;> decide +kernel)
private theorem dfg_base (unsigned maximum : Bool) : DFGCons (built unsigned maximum).1 (frame unsigned maximum) := by
  have absentX : (built unsigned maximum).1.defInst? 7 = none := by cases unsigned <;> cases maximum <;> rfl
  have absentY : (built unsigned maximum).1.defInst? 31 = none := by cases unsigned <;> cases maximum <;> rfl
  have typeX : (built unsigned maximum).1.valueType? 7 = some (.int 64) := by cases unsigned <;> cases maximum <;> rfl
  have typeY : (built unsigned maximum).1.valueType? 31 = some (.int 64) := by cases unsigned <;> cases maximum <;> rfl
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      rw [absentX] at defined
      cases defined
    · by_cases thirtyone : x = 31
      · subst x
        rw [absentY] at defined
        cases defined
      · simp [frame,seven,thirtyone] at lookup
  · intro x t v typed lookup
    by_cases seven : x = 7
    · subst x
      rw [typeX] at typed
      cases typed
      cases lookup
      rfl
    · by_cases thirtyone : x = 31
      · subst x
        rw [typeY] at typed
        cases typed
        cases lookup
        rfl
      · simp [frame,seven,thirtyone] at lookup
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
private structure Inputs (unsigned maximum : Bool) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower ((function unsigned maximum)) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = (0 : Nat)
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.binary (minmaxOperation unsigned maximum) .i64 7 31)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int)
  typeX : event.ctx.valueType? 7 = some (.int 64)
  typeY : event.ctx.valueType? 31 = some (.int 64)
  parameterX : event.ctx.defInst? 7 = none
  parameterY : event.ctx.defInst? 31 = none
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (minmaxRule unsigned maximum).id
  dfg : DFGCons event.ctx (frame unsigned maximum)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame unsigned maximum)
    (fun k => regs unsigned maximum (aliasNum result.final.alias k))

private theorem inputs (unsigned maximum : Bool) :
    Nonempty (Inputs unsigned maximum) := by
  have actual := observed unsigned maximum
  cases run : Stock.lower ((function unsigned maximum)) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,stepData⟩ := actual
    simp only [ctxKey,minmaxCtxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some (minmaxRule unsigned maximum).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.binary (minmaxOperation unsigned maximum) .i64 7 31),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      cases unsigned <;> cases maximum <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.binary (minmaxOperation unsigned maximum) .i64 7 31) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int) := by
      simp only [Ctx.valueReg?,maps]
      cases unsigned <;> cases maximum <;> rfl
    have typeX : event.ctx.valueType? 7 = some (.int 64) := by simp only [Ctx.valueType?,types]; cases unsigned <;> cases maximum <;> rfl
    have typeY : event.ctx.valueType? 31 = some (.int 64) := by simp only [Ctx.valueType?,types]; cases unsigned <;> cases maximum <;> rfl
    have parameterX : event.ctx.defInst? 7 = none := by simp only [Ctx.defInst?,defs]; cases unsigned <;> cases maximum <;> rfl
    have parameterY : event.ctx.defInst? 31 = none := by simp only [Ctx.defInst?,defs]; cases unsigned <;> cases maximum <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame unsigned maximum)
        (fun n => regs unsigned maximum (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt .i64 (-7)) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          cases unsigned <;> cases maximum <;> rfl
        · dsimp only
          rw [alias192]
          cases unsigned <;> cases maximum <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          change some (.ofInt .i64 9) = some val at lookup
          cases lookup
          refine ⟨193,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            cases unsigned <;> cases maximum <;> rfl
          · dsimp only
            rw [alias193]
            cases unsigned <;> cases maximum <;> unfold VHolds <;> decide +kernel
        · simp [frame,seven,thirtyone] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,typeX,typeY,parameterX,parameterY,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base unsigned maximum),held⟩⟩

private theorem dominated (unsigned maximum : Bool) : Dominated (function unsigned maximum) := by
  constructor
  · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function,minmaxFunction] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        change y ∈ [7,31] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> simp [availOf,function,minmaxFunction,defsBefore,defsFrom]
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        simp [availOf,function,minmaxFunction,defsBefore,defsFrom]
    | succ bi => simp [function,minmaxFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := (function unsigned maximum)) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function unsigned maximum).blocks.length = 1 := rfl
    omega
private theorem frame_available (unsigned maximum : Bool) (ctx : Ctx) :
    (restrict (frame unsigned maximum) (availOf (function unsigned maximum) (availIn (function unsigned maximum) ctx) 0 0)).regs = (frame unsigned maximum).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,minmaxFunction,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]
private theorem restrictedDFG (unsigned maximum : Bool) (input : Inputs unsigned maximum) :
    DFGCons input.event.ctx (restrict (frame unsigned maximum) (availOf (function unsigned maximum) (availIn (function unsigned maximum) input.result.ctx) 0 0)) :=
  dfgCons_congr (ctx := input.event.ctx) (fr := frame unsigned maximum) rfl rfl (frame_available unsigned maximum input.result.ctx) input.dfg
private theorem getX (unsigned maximum : Bool) (ctx : Ctx) :
    (restrict (frame unsigned maximum) (availOf (function unsigned maximum) (availIn (function unsigned maximum) ctx) 0 0)).getAs 7 .i64 = .ok (BitVec.ofInt 64 (-7)) := by
  have same := getAs_congr (fr := frame unsigned maximum)
    (fr' := restrict (frame unsigned maximum) (availOf (function unsigned maximum) (availIn (function unsigned maximum) ctx) 0 0))
    (x := 7) (ty := .i64) (congrFun (frame_available unsigned maximum ctx) 7)
  exact same.trans rfl
private theorem getY (unsigned maximum : Bool) (ctx : Ctx) :
    (restrict (frame unsigned maximum) (availOf (function unsigned maximum) (availIn (function unsigned maximum) ctx) 0 0)).getAs 31 .i64 =
      .ok (BitVec.ofNat 64 9) := by
  have same := getAs_congr (fr := frame unsigned maximum)
    (fr' := restrict (frame unsigned maximum) (availOf (function unsigned maximum) (availIn (function unsigned maximum) ctx) 0 0))
    (x := 31) (ty := .i64) (congrFun (frame_available unsigned maximum ctx) 31)
  cases unsigned <;> cases maximum <;> exact same.trans rfl
private theorem current (unsigned maximum : Bool) (input : Inputs unsigned maximum) :
    input.record.inst = blockStart (function unsigned maximum) 0 + (0 : Nat) := by
  simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
private theorem guarded (unsigned maximum : Bool) (input : Inputs unsigned maximum) :
    ValuesHeld (fun v => Demanded input.record.output.state v ∧ v ∈ availOf (function unsigned maximum) (availIn (function unsigned maximum) input.result.ctx) 0 0)
      input.event.ctx (frame unsigned maximum) (fun key => regs unsigned maximum (aliasNum input.result.final.alias key)) :=
  input.held.mono (fun _ needed => needed.1)
/-- All four complete actual retained Stock.lower min/max functions and original source step
inhabit fresh result binding, original guarded source transfer and original min/max
execution, with dirty upper input bits and sparse original source numbering. -/
theorem stock_minmax_register_complete_source_witness (unsigned maximum : Bool) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower (function unsigned maximum) = .ok result ∧ LowerScope (function unsigned maximum) ∧ Dominated (function unsigned maximum) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some (minmaxRule unsigned maximum).id ∧
      step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame unsigned maximum,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs unsigned maximum) world (fun ρ' _ =>
          VHolds ⟨.i64,Clif.Sem.binary (minmaxOperation unsigned maximum) (BitVec.ofInt 64 (-7)) 9⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = regs unsigned maximum k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf (function unsigned maximum) (availIn (function unsigned maximum) result.ctx) 0 1) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs unsigned maximum
  let value : Clif.Val := ⟨.i64,Clif.Sem.binary (minmaxOperation unsigned maximum) (BitVec.ofInt 64 (-7)) 9⟩
  let fr' : Clif.Frame := {frame unsigned maximum with regs := (frame unsigned maximum).regs.set 100 value,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame unsigned maximum) Clif.Mem.empty (.binary (minmaxOperation unsigned maximum) .i64 7 31) =
      .ok ([value],Clif.Mem.empty) := by cases unsigned <;> cases maximum <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame unsigned maximum,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.binary (minmaxOperation unsigned maximum) .i64 7 31,[value],(frame unsigned maximum).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    · rw [input.results]; rfl
    · rw [input.results]; rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨u,v,originalX,originalY,d,output,lower,upper,memory,execution⟩ := stock_lower_minmax_register_source_with_reads input.run (scope unsigned maximum) (dominated unsigned maximum) input.events input.records
    (bi := 0) (j := 0) (block := (function unsigned maximum).blocks[0]!) rfl rfl (current unsigned maximum input) unsigned maximum input.source input.clif true rfl
    input.typeX input.typeY
    (by intro j info defn found ty value; rw [input.parameterX] at defn; cases defn)
    (by intro j info defn found ty value; rw [input.parameterY] at defn; cases defn) input.results rfl input.mapped input.recorded input.emitted
    self (restrictedDFG unsigned maximum input) (guarded unsigned maximum input) sourceStep
  have sameX := Clif.Res.ok.inj (originalX.symm.trans (getX unsigned maximum input.result.ctx))
  have sameY := Clif.Res.ok.inj (originalY.symm.trans (getY unsigned maximum input.result.ctx))
  subst u
  subst v
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,scope unsigned maximum,dominated unsigned maximum,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,lower,upper,sourceStep,execution⟩
end Backend.Stock.Proof.ScalarSelect.MinMaxDriverWitness
