import FV.Backend.Proof.StockMinMaxNarrowDriverRuns
import FV.Backend.Proof.StockMinMaxActualDispatch
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.ScalarSelect.MinMaxNarrowDriverWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarSelect Backend.Stock.Proof.ScalarSelect.MinMaxRegisterFixture
open Backend.Stock.Proof.ScalarCmp
private abbrev function := narrowMinmaxFunction
private abbrev built := narrowMinmaxBuilt
private abbrev sourceKey := minmaxSourceKey
private abbrev ctxKey := minmaxCtxKey
private abbrev observed := stock_minmax_narrow_driver_observed
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frame (unsigned maximum half : Bool) : Clif.Frame := {
  func := (function unsigned maximum half)
  regs := fun x => if x = 7 then some (.ofInt (narrowMinmaxTy half) (-7)) else
    if x = 31 then some (.ofInt (narrowMinmaxTy half) 9) else none
  slots := [],body := [⟨[100],.binary (minmaxOperation unsigned maximum) (narrowMinmaxTy half) 7 31⟩],term := .ret [100] }
private def regs (unsigned maximum half : Bool) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+(BitVec.ofInt (narrowMinmaxTy half).width (-7)).toNat)
  else if n = 193 then BitVec.ofNat 128 (2^100+9) else 0
private theorem scope (unsigned maximum half : Bool) : LowerScope (function unsigned maximum half) := lowerScope_of (by cases unsigned <;> cases maximum <;> cases half <;> decide +kernel)
private theorem dfg_base (unsigned maximum half : Bool) : DFGCons (built unsigned maximum half).1 (frame unsigned maximum half) := by
  have absentX : (built unsigned maximum half).1.defInst? 7 = none := by cases unsigned <;> cases maximum <;> cases half <;> rfl
  have absentY : (built unsigned maximum half).1.defInst? 31 = none := by cases unsigned <;> cases maximum <;> cases half <;> rfl
  have typeX : (built unsigned maximum half).1.valueType? 7 = some (.int (narrowMinmaxTy half).width) := by cases unsigned <;> cases maximum <;> cases half <;> rfl
  have typeY : (built unsigned maximum half).1.valueType? 31 = some (.int (narrowMinmaxTy half).width) := by cases unsigned <;> cases maximum <;> cases half <;> rfl
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
      cases half <;> rfl
    · by_cases thirtyone : x = 31
      · subst x
        rw [typeY] at typed
        cases typed
        cases lookup
        cases half <;> rfl
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
private structure Inputs (unsigned maximum half : Bool) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower ((function unsigned maximum half)) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = (0 : Nat)
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.binary (minmaxOperation unsigned maximum) (narrowMinmaxTy half) 7 31)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int)
  typeX : event.ctx.valueType? 7 = some (.int (narrowMinmaxTy half).width)
  typeY : event.ctx.valueType? 31 = some (.int (narrowMinmaxTy half).width)
  parameterX : event.ctx.defInst? 7 = none
  parameterY : event.ctx.defInst? 31 = none
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (minmaxRule unsigned maximum).id
  dfg : DFGCons event.ctx (frame unsigned maximum half)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame unsigned maximum half)
    (fun k => regs unsigned maximum half (aliasNum result.final.alias k))

private theorem inputs (unsigned maximum half : Bool) :
    Nonempty (Inputs unsigned maximum half) := by
  have actual := observed unsigned maximum half
  cases run : Stock.lower ((function unsigned maximum half)) with
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
        some (some (.binary (minmaxOperation unsigned maximum) (narrowMinmaxTy half) 7 31),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      cases unsigned <;> cases maximum <;> cases half <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.binary (minmaxOperation unsigned maximum) (narrowMinmaxTy half) 7 31) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int) := by
      simp only [Ctx.valueReg?,maps]
      cases unsigned <;> cases maximum <;> cases half <;> rfl
    have typeX : event.ctx.valueType? 7 = some (.int (narrowMinmaxTy half).width) := by simp only [Ctx.valueType?,types]; cases unsigned <;> cases maximum <;> cases half <;> rfl
    have typeY : event.ctx.valueType? 31 = some (.int (narrowMinmaxTy half).width) := by simp only [Ctx.valueType?,types]; cases unsigned <;> cases maximum <;> cases half <;> rfl
    have parameterX : event.ctx.defInst? 7 = none := by simp only [Ctx.defInst?,defs]; cases unsigned <;> cases maximum <;> cases half <;> rfl
    have parameterY : event.ctx.defInst? 31 = none := by simp only [Ctx.defInst?,defs]; cases unsigned <;> cases maximum <;> cases half <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame unsigned maximum half)
        (fun n => regs unsigned maximum half (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt (narrowMinmaxTy half) (-7)) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          cases unsigned <;> cases maximum <;> cases half <;> rfl
        · dsimp only
          rw [alias192]
          cases unsigned <;> cases maximum <;> cases half <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          change some (.ofInt (narrowMinmaxTy half) 9) = some val at lookup
          cases lookup
          refine ⟨193,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            cases unsigned <;> cases maximum <;> cases half <;> rfl
          · dsimp only
            rw [alias193]
            cases unsigned <;> cases maximum <;> cases half <;> unfold VHolds <;> decide +kernel
        · simp [frame,seven,thirtyone] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,typeX,typeY,parameterX,parameterY,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base unsigned maximum half),held⟩⟩

private theorem dominated (unsigned maximum half : Bool) : Dominated (function unsigned maximum half) := by
  constructor
  · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function,narrowMinmaxFunction] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        change y ∈ [7,31] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> simp [availOf,function,narrowMinmaxFunction,defsBefore,defsFrom]
      · intro y member
        have members : y ∈ [100] := by cases half <;> exact member
        have equal := List.mem_singleton.mp members
        subst y
        simp [availOf,function,narrowMinmaxFunction,defsBefore,defsFrom]
    | succ bi => simp [function,narrowMinmaxFunction] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := (function unsigned maximum half)) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function unsigned maximum half).blocks.length = 1 := rfl
    omega
private theorem frame_available (unsigned maximum half : Bool) (ctx : Ctx) :
    (restrict (frame unsigned maximum half) (availOf (function unsigned maximum half) (availIn (function unsigned maximum half) ctx) 0 0)).regs = (frame unsigned maximum half).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,narrowMinmaxFunction,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]
private theorem restrictedDFG (unsigned maximum half : Bool) (input : Inputs unsigned maximum half) :
    DFGCons input.event.ctx (restrict (frame unsigned maximum half) (availOf (function unsigned maximum half) (availIn (function unsigned maximum half) input.result.ctx) 0 0)) :=
  dfgCons_congr (ctx := input.event.ctx) (fr := frame unsigned maximum half) rfl rfl (frame_available unsigned maximum half input.result.ctx) input.dfg
private theorem getX (unsigned maximum half : Bool) (ctx : Ctx) :
    (restrict (frame unsigned maximum half) (availOf (function unsigned maximum half) (availIn (function unsigned maximum half) ctx) 0 0)).getAs 7 (narrowMinmaxTy half) = .ok (BitVec.ofInt (narrowMinmaxTy half).width (-7)) := by
  have same := getAs_congr (fr := frame unsigned maximum half)
    (fr' := restrict (frame unsigned maximum half) (availOf (function unsigned maximum half) (availIn (function unsigned maximum half) ctx) 0 0))
    (x := 7) (ty := (narrowMinmaxTy half)) (congrFun (frame_available unsigned maximum half ctx) 7)
  cases half <;> exact same.trans rfl
private theorem getY (unsigned maximum half : Bool) (ctx : Ctx) :
    (restrict (frame unsigned maximum half) (availOf (function unsigned maximum half) (availIn (function unsigned maximum half) ctx) 0 0)).getAs 31 (narrowMinmaxTy half) =
      .ok (BitVec.ofNat (narrowMinmaxTy half).width 9) := by
  have same := getAs_congr (fr := frame unsigned maximum half)
    (fr' := restrict (frame unsigned maximum half) (availOf (function unsigned maximum half) (availIn (function unsigned maximum half) ctx) 0 0))
    (x := 31) (ty := (narrowMinmaxTy half)) (congrFun (frame_available unsigned maximum half ctx) 31)
  cases unsigned <;> cases maximum <;> cases half <;> exact same.trans rfl
private theorem current (unsigned maximum half : Bool) (input : Inputs unsigned maximum half) :
    input.record.inst = blockStart (function unsigned maximum half) 0 + (0 : Nat) := by
  simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
private theorem guarded (unsigned maximum half : Bool) (input : Inputs unsigned maximum half) :
    ValuesHeld (fun v => Demanded input.record.output.state v ∧ v ∈ availOf (function unsigned maximum half) (availIn (function unsigned maximum half) input.result.ctx) 0 0)
      input.event.ctx (frame unsigned maximum half) (fun key => regs unsigned maximum half (aliasNum input.result.final.alias key)) :=
  input.held.mono (fun _ needed => needed.1)
/-- All four complete actual retained Stock.lower min/max functions and original source step
inhabit fresh result binding, original guarded source transfer and original min/max
execution, with dirty upper input bits and sparse original source numbering. -/
theorem stock_minmax_narrow_complete_source_witness (unsigned maximum half : Bool) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower (function unsigned maximum half) = .ok result ∧ LowerScope (function unsigned maximum half) ∧ Dominated (function unsigned maximum half) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some (minmaxRule unsigned maximum).id ∧
      step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame unsigned maximum half,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs unsigned maximum half) world (fun ρ' _ =>
          VHolds ⟨(narrowMinmaxTy half),Clif.Sem.binary (minmaxOperation unsigned maximum) (BitVec.ofInt (narrowMinmaxTy half).width (-7)) 9⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = regs unsigned maximum half k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf (function unsigned maximum half) (availIn (function unsigned maximum half) result.ctx) 0 1) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs unsigned maximum half
  let value : Clif.Val := ⟨(narrowMinmaxTy half),Clif.Sem.binary (minmaxOperation unsigned maximum) (BitVec.ofInt (narrowMinmaxTy half).width (-7)) 9⟩
  let fr' : Clif.Frame := {frame unsigned maximum half with regs := (frame unsigned maximum half).regs.set 100 value,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame unsigned maximum half) Clif.Mem.empty (.binary (minmaxOperation unsigned maximum) (narrowMinmaxTy half) 7 31) =
      .ok ([value],Clif.Mem.empty) := by cases unsigned <;> cases maximum <;> cases half <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame unsigned maximum half,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.binary (minmaxOperation unsigned maximum) (narrowMinmaxTy half) 7 31,[value],(frame unsigned maximum half).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    · rw [input.results]; rfl
    · rw [input.results]; rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨u,v,originalX,originalY,d,output,lower,upper,memory,execution⟩ := stock_lower_minmax_actual_source_with_reads input.run (scope unsigned maximum half) (dominated unsigned maximum half) input.events input.records
    (bi := 0) (j := 0) (block := (function unsigned maximum half).blocks[0]!) rfl rfl (current unsigned maximum half input) unsigned maximum input.source input.clif
    (by cases half <;> exact input.typeX) (by cases half <;> exact input.typeY)
    input.results rfl input.mapped input.recorded input.emitted
    self (restrictedDFG unsigned maximum half input) (guarded unsigned maximum half input) sourceStep
  have sameX := Clif.Res.ok.inj (originalX.symm.trans (getX unsigned maximum half input.result.ctx))
  have sameY := Clif.Res.ok.inj (originalY.symm.trans (getY unsigned maximum half input.result.ctx))
  subst u
  subst v
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,scope unsigned maximum half,dominated unsigned maximum half,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,lower,upper,sourceStep,execution⟩
end Backend.Stock.Proof.ScalarSelect.MinMaxNarrowDriverWitness
