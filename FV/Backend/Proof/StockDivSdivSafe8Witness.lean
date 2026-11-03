import FV.Backend.Proof.StockDivSdivSafe8WitnessRuns
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.ScalarDiv.SdivSafe8Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open RunData
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frame (trapping : Bool) : Clif.Frame := {
  func := function
  regs := fun x => if x = 7 then some (.ofInt .i8 (-27)) else
    if x = 31 then some (.ofInt .i8 9) else none
  slots := [],body := [⟨[100],.div .sdiv .i8 7 31⟩],term := .ret [100] }
private def regs (trapping : Bool) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+(BitVec.ofInt 8 (-27)).toNat)
  else if n = 193 then BitVec.ofNat 128 (2^100+777) else 0
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
        have definition : (built).1.defInst? 31 = some 0 := by rfl
        rw [definition] at defined
        cases defined
        have infoEq : info = built.1.insts[0]! := Option.some.inj (found.symm.trans (by rfl))
        subst info
        change some (.iconst .i8 (9#8)) = some cl at original
        cases original
        change some (.ofInt .i8 9) = some v at lookup
        cases lookup
        exact ⟨[⟨.i8,9#8⟩],fun _ => rfl,rfl⟩
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
  current : record.inst = (1 : Nat)
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.div .sdiv .i8 7 31)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some rule_lower_1167.id
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
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,ignored,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some rule_lower_1167.id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.div .sdiv .i8 7 31),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.div .sdiv .i8 7 31) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int) := by
      simp only [Ctx.valueReg?,maps]
      rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame trapping)
        (fun n => regs trapping (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt .i8 (-27)) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rfl
        · dsimp only
          rw [alias192]
          cases trapping <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          change some (.ofInt .i8 9) = some val at lookup
          cases lookup
          refine ⟨193,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            rfl
          · exact False.elim (needed ignored)
        · simp [frame,seven,thirtyone] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base trapping),held⟩⟩

private theorem dominated : Dominated function := by
  constructor
  · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j with
        | zero =>
          simp at statement
          subst stm
          simp [Driver.instArgs] at member
        | succ j =>
          cases j <;> simp at statement
          subst stm
          change y ∈ [7,31] at member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 1 := rfl
    omega
private theorem frame_available (trapping : Bool) (ctx : Ctx) :
    (restrict (frame trapping) (availOf function (availIn function ctx) 0 1)).regs = (frame trapping).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]
private theorem restrictedDFG (trapping : Bool) (input : Inputs trapping) :
    DFGCons input.event.ctx (restrict (frame trapping) (availOf function (availIn function input.result.ctx) 0 1)) :=
  dfgCons_congr (ctx := input.event.ctx) (fr := frame trapping) rfl rfl (frame_available trapping input.result.ctx) input.dfg
private theorem getX (trapping : Bool) (ctx : Ctx) :
    (restrict (frame trapping) (availOf function (availIn function ctx) 0 1)).getAs 7 .i8 = .ok (BitVec.ofInt 8 (-27)) := by
  have same := getAs_congr (fr := frame trapping)
    (fr' := restrict (frame trapping) (availOf function (availIn function ctx) 0 1))
    (x := 7) (ty := .i8) (congrFun (frame_available trapping ctx) 7)
  exact same.trans rfl
private theorem getY (trapping : Bool) (ctx : Ctx) :
    (restrict (frame trapping) (availOf function (availIn function ctx) 0 1)).getAs 31 .i8 =
      .ok (BitVec.ofNat 8 9) := by
  have same := getAs_congr (fr := frame trapping)
    (fr' := restrict (frame trapping) (availOf function (availIn function ctx) 0 1))
    (x := 31) (ty := .i8) (congrFun (frame_available trapping ctx) 31)
  cases trapping <;> exact same.trans rfl
private theorem current (trapping : Bool) (input : Inputs trapping) :
    input.record.inst = blockStart function 0 + (1 : Nat) := by
  simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
private theorem guarded (trapping : Bool) (input : Inputs trapping) :
    ValuesHeld (fun v => Demanded input.record.output.state v ∧ v ∈ availOf function (availIn function input.result.ctx) 0 1)
      input.event.ctx (frame trapping) (fun key => regs trapping (aliasNum input.result.final.alias key)) :=
  input.held.mono (fun _ needed => needed.1)
/-- A real complete retained unsigned division record and successful original
source step execute quotient2, preserve source memory and every other required
available value, with dirty upper machine-register bits. -/
theorem stock_sdiv_safe_8_success_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_1167.id ∧
      step.results = [[.vreg d .int]] ∧ (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame false,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs false) world (fun ρ' _ =>
          VHolds ⟨.i8,(BitVec.ofInt 8 (-3))⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = regs false k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf function (availIn function result.ctx) 0 2) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs false
  let value : Clif.Val := ⟨.i8,(BitVec.ofInt 8 (-3))⟩
  let fr' : Clif.Frame := {frame false with regs := (frame false).regs.set 100 value,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame false) Clif.Mem.empty (.div .sdiv .i8 7 31) =
      .ok ([value],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame false,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.div .sdiv .i8 7 31,[value],(frame false).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    · rw [input.results]; rfl
    · rw [input.results]; rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨d,q,output,bounds,divided,memory,execution⟩ := stock_lower_sdiv_available_source (ty := .i8) input.run scope dominated input.events input.records
    (bi := 0) (j := 1) (block := function.blocks[0]!) rfl rfl (current false input) input.source input.clif input.results rfl
    input.mapped input.recorded input.emitted self (restrictedDFG false input) (guarded false input)
    (getX false input.result.ctx) (getY false input.result.ctx) sourceStep
  have result : q = (BitVec.ofInt 8 (-3)) := Except.ok.inj (divided.symm.trans (show Clif.Sem.div .sdiv (BitVec.ofInt 8 (-27)) (9#8) = .ok ((BitVec.ofInt 8 (-3))) from rfl))
  subst q
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,scope,dominated,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,bounds,sourceStep,execution⟩
end Backend.Stock.Proof.ScalarDiv.SdivSafe8Witness
