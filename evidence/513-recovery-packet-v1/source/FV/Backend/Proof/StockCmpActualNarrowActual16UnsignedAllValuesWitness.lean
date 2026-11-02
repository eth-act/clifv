import FV.Backend.Proof.StockCmpActualDispatch
import FV.Backend.Proof.StockCmpNarrow16DriverRuns
import FV.Backend.Proof.StockCmpNarrowActualOriginalSourceValues
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.ScalarCmp.ActualNarrowActual16UnsignedAllValuesWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
private abbrev function := cmpNarrow16Function false
private abbrev built := cmpNarrow16Built false
private abbrev sourceKey := cmpSourceKey
private abbrev ctxKey := cmpCtxKey
private abbrev observed := stock_cmp_narrow16_driver_observed false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frame (leftWord rightWord : BitVec 16) : Clif.Frame := {
  func := function
  regs := fun x => if x = 7 then some ⟨.i16,leftWord⟩ else if x = 31 then some ⟨.i16,rightWord⟩ else none
  slots := [],body := [⟨[100],.icmp .ult .i16 7 31⟩],term := .ret [100] }
private def regs (leftWord rightWord : BitVec 16) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+leftWord.toNat)
  else if n = 193 then BitVec.ofNat 128 (2^100+rightWord.toNat) else 0
private theorem dirty_low (word : BitVec 16) :
    (BitVec.ofNat 128 (2^100+word.toNat)).setWidth 16 = word := by
  rw [BitVec.setWidth_ofNat_of_le (by decide)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.add_mod,show 2^100 % 2^16 = 0 from by decide +kernel,
    Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem dfg_base (leftWord rightWord : BitVec 16) : DFGCons (built).1 (frame leftWord rightWord) := by
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
private structure Inputs (leftWord rightWord : BitVec 16) where
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
  clif : info.clif = some (.icmp .ult .i16 7 31)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int)
  typeX : event.ctx.valueType? 7 = some (.int 16)
  typeY : event.ctx.valueType? 31 = some (.int 16)
  parameterX : event.ctx.defInst? 7 = none
  parameterY : event.ctx.defInst? 31 = none
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some rule_lower_2215.id
  dfg : DFGCons event.ctx (frame leftWord rightWord)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame leftWord rightWord)
    (fun k => regs leftWord rightWord (aliasNum result.final.alias k))

private theorem inputs (leftWord rightWord : BitVec 16) :
    Nonempty (Inputs leftWord rightWord) := by
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
        some (some (.icmp .ult .i16 7 31),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.icmp .ult .i16 7 31) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int) := by
      simp only [Ctx.valueReg?,maps]
      rfl
    have typeX : event.ctx.valueType? 7 = some (.int 16) := by simp only [Ctx.valueType?,types]; rfl
    have typeY : event.ctx.valueType? 31 = some (.int 16) := by simp only [Ctx.valueType?,types]; rfl
    have parameterX : event.ctx.defInst? 7 = none := by simp only [Ctx.defInst?,defs]; rfl
    have parameterY : event.ctx.defInst? 31 = none := by simp only [Ctx.defInst?,defs]; rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame leftWord rightWord)
        (fun n => regs leftWord rightWord (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (⟨.i16,leftWord⟩) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rfl
        · dsimp only
          rw [alias192]
          change (BitVec.ofNat 128 (2^100+leftWord.toNat)).setWidth 16 = leftWord
          exact dirty_low leftWord
      · by_cases thirtyone : x = 31
        · subst x
          change some (⟨.i16,rightWord⟩) = some val at lookup
          cases lookup
          refine ⟨193,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            rfl
          · dsimp only
            rw [alias193]
            change (BitVec.ofNat 128 (2^100+rightWord.toNat)).setWidth 16 = rightWord
            exact dirty_low rightWord
        · simp [frame,seven,thirtyone] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,typeX,typeY,parameterX,parameterY,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base leftWord rightWord),held⟩⟩

private theorem dominated : Dominated function := by
  constructor
  · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function,cmpNarrow16Function] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        change y ∈ [7,31] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> simp [availOf,function,cmpNarrow16Function,defsBefore,defsFrom]
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        simp [availOf,function,cmpNarrow16Function,defsBefore,defsFrom]
    | succ bi => simp [function,cmpNarrow16Function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 1 := rfl
    omega
private theorem frame_available (leftWord rightWord : BitVec 16) (ctx : Ctx) :
    (restrict (frame leftWord rightWord) (availOf function (availIn function ctx) 0 0)).regs = (frame leftWord rightWord).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,cmpNarrow16Function,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]
private theorem restrictedDFG (leftWord rightWord : BitVec 16) (input : Inputs leftWord rightWord) :
    DFGCons input.event.ctx (restrict (frame leftWord rightWord) (availOf function (availIn function input.result.ctx) 0 0)) :=
  dfgCons_congr (ctx := input.event.ctx) (fr := frame leftWord rightWord) rfl rfl (frame_available leftWord rightWord input.result.ctx) input.dfg
private theorem getX (leftWord rightWord : BitVec 16) (ctx : Ctx) :
    (restrict (frame leftWord rightWord) (availOf function (availIn function ctx) 0 0)).getAs 7 .i16 = .ok leftWord := by
  have same := getAs_congr (fr := frame leftWord rightWord)
    (fr' := restrict (frame leftWord rightWord) (availOf function (availIn function ctx) 0 0))
    (x := 7) (ty := .i16) (congrFun (frame_available leftWord rightWord ctx) 7)
  exact same.trans rfl
private theorem getY (leftWord rightWord : BitVec 16) (ctx : Ctx) :
    (restrict (frame leftWord rightWord) (availOf function (availIn function ctx) 0 0)).getAs 31 .i16 =
      .ok rightWord := by
  have same := getAs_congr (fr := frame leftWord rightWord)
    (fr' := restrict (frame leftWord rightWord) (availOf function (availIn function ctx) 0 0))
    (x := 31) (ty := .i16) (congrFun (frame_available leftWord rightWord ctx) 31)
  exact same.trans rfl
private theorem current (leftWord rightWord : BitVec 16) (input : Inputs leftWord rightWord) :
    input.record.inst = blockStart function 0 + (0 : Nat) := by
  simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
private theorem guarded (leftWord rightWord : BitVec 16) (input : Inputs leftWord rightWord) :
    ValuesHeld (fun v => Demanded input.record.output.state v ∧ v ∈ availOf function (availIn function input.result.ctx) 0 0)
      input.event.ctx (frame leftWord rightWord) (fun key => regs leftWord rightWord (aliasNum input.result.final.alias key)) :=
  input.held.mono (fun _ needed => needed.1)
/-- Complete actual Stock.lower retained-record and original source-step
execution at16 bits for arbitrary input words, including scratch separation
derived from original availability, dirty upper bits and guarded postavailability. -/
theorem stock_cmp_actual_narrow_actual16_unsigned_complete_source_witness_all_values
    (leftWord rightWord : BitVec 16) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_2215.id ∧
      step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame leftWord rightWord,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs leftWord rightWord) world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .ult leftWord rightWord)⟩ (ρ' d) ∧
          (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = regs leftWord rightWord k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf function (availIn function result.ctx) 0 1) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs leftWord rightWord
  let value : Clif.Val := ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .ult leftWord rightWord)⟩
  let fr' : Clif.Frame := {frame leftWord rightWord with regs := (frame leftWord rightWord).regs.set 100 value,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame leftWord rightWord) Clif.Mem.empty (.icmp .ult .i16 7 31) =
      .ok ([value],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame leftWord rightWord,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.icmp .ult .i16 7 31,[value],(frame leftWord rightWord).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    · rw [input.results]; rfl
    · rw [input.results]; rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨originalLeft,originalRight,d,readLeft,readRight,output,lower,upper,memory,execution⟩ :=
    stock_lower_cmp_actual_source_by_instruction input.run scope dominated input.events input.records
    (bi := 0) (j := 0) (block := function.blocks[0]!) rfl rfl (current leftWord rightWord input) input.source input.clif
    input.typeX input.typeY input.results rfl input.mapped input.recorded input.emitted
    self (restrictedDFG leftWord rightWord input) (guarded leftWord rightWord input) sourceStep
  rw [getX leftWord rightWord input.result.ctx] at readLeft
  cases readLeft
  rw [getY leftWord rightWord input.result.ctx] at readRight
  cases readRight
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,scope,dominated,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,lower,upper,sourceStep,execution⟩
end Backend.Stock.Proof.ScalarCmp.ActualNarrowActual16UnsignedAllValuesWitness
