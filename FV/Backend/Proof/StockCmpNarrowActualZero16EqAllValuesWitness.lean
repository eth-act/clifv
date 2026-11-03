import FV.Backend.Proof.StockCmpNarrowActualOriginalSourceValues
import FV.Backend.Proof.StockCmpZero16DriverRuns
import FV.Backend.Proof.StockCmpZero16Transfer
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.ScalarCmp.NarrowActualZero16EqAllValuesWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarCmp
private abbrev function := cmpZero16Function false
private abbrev built := cmpZero16Built false
private abbrev sourceKey := cmpSourceKey
private abbrev ctxKey := cmpCtxKey
private abbrev observed := stock_cmp_zero16_driver_observed false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frame (word : BitVec 16) : Clif.Frame := {
  func := function
  regs := fun x => if x = 7 then some (⟨.i16,word⟩) else
    if x = 31 then some (.ofInt .i16 0) else none
  slots := [],body := [⟨[100],.icmp .eq .i16 7 31⟩],term := .ret [100] }
private def regs (word : BitVec 16) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+word.toNat)
  else if n = 193 then BitVec.ofNat 128 (2^100+777) else 0
section KernelFacts
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem definedNegKey : (built.1.insts[0]?).map sourceKey = some (some (.iconst .i16 (BitVec.ofNat 16 0)),[31]) := by
  decide +kernel
end KernelFacts
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem dfg_base (word : BitVec 16) : DFGCons (built).1 (frame word) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : (built).1.defInst? 7 = none := by rfl
      rw [absent] at defined; cases defined
    · by_cases thirtyone : x = 31
      · subst x
        change some 0 = some j at defined
        cases defined
        obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
        subst info
        cases original
        cases lookup
        exact ⟨[.ofInt .i16 0],fun cm => rfl,rfl⟩
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
private structure Inputs (word : BitVec 16) where
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
  clif : info.clif = some (.icmp .eq .i16 7 31)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int)
  typeX : event.ctx.valueType? 7 = some (.int 16)
  typeY : event.ctx.valueType? 31 = some (.int 16)
  parameter : event.ctx.defInst? 7 = none
  constantInfo : IInfo
  defined : event.ctx.defInst? 31 = some 0
  constantFound : event.ctx.insts[0]? = some constantInfo
  constantData : constantInfo.data = .data 152 35 [.data 151 57 [],.int 0]
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some rule_lower_2215.id
  dfg : DFGCons event.ctx (frame word)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame word)
    (fun k => regs word (aliasNum result.final.alias k))

private theorem inputs (word : BitVec 16) :
    Nonempty (Inputs word) := by
  have actual := observed
  cases run : Stock.lower (function) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,constantPayload,record,records,current,undemanded,stepData⟩ := actual
    simp only [ctxKey,cmpCtxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some rule_lower_2215.id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.icmp .eq .i16 7 31),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.icmp .eq .i16 7 31) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int) := by
      simp only [Ctx.valueReg?,maps]
      rfl
    have typeX : event.ctx.valueType? 7 = some (.int 16) := by simp only [Ctx.valueType?,types]; rfl
    have typeY : event.ctx.valueType? 31 = some (.int 16) := by simp only [Ctx.valueType?,types]; rfl
    have parameter : event.ctx.defInst? 7 = none := by simp only [Ctx.defInst?,defs]; rfl
    obtain ⟨constantInfo,constantFound,constantData⟩ := Option.map_eq_some_iff.mp constantPayload
    have defined : event.ctx.defInst? 31 = some 0 := by simp only [Ctx.defInst?,defs]; rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame word)
        (fun n => regs word (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (⟨.i16,word⟩) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rfl
        · dsimp only
          rw [alias192]
          change (BitVec.ofNat 128 (2^100+word.toNat)).setWidth 16 = word
          rw [BitVec.setWidth_ofNat_of_le (by decide)]
          apply BitVec.eq_of_toNat_eq
          simp only [BitVec.toNat_ofNat,Nat.add_mod,show 2^100 % 2^16 = 0 from by decide +kernel,
            Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
      · by_cases thirtyone : x = 31
        · subst x
          unfold Demanded at needed
          rw [undemanded] at needed
          omega
        · simp [frame,seven,thirtyone] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,typeX,typeY,parameter,constantInfo,defined,constantFound,constantData,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base word),held⟩⟩

private theorem dominated : Dominated function := by
  constructor
  · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function,cmpZero16Function] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j with
        | zero =>
          simp at statement
          subst stm
          change y ∈ ([] : List Nat) at member
          cases member
        | succ j =>
          cases j with
          | zero =>
            simp at statement
            subst stm
            change y ∈ [7,31] at member
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl <;> simp [availOf,function,cmpZero16Function,defsBefore,defsFrom]
          | succ j => simp at statement
      · intro y member
        change y ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst y
        simp [availOf,function,cmpZero16Function,defsBefore,defsFrom]
    | succ bi => simp [function,cmpZero16Function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 1 := rfl
    omega
private theorem frame_available (word : BitVec 16) (ctx : Ctx) :
    (restrict (frame word) (availOf function (availIn function ctx) 0 1)).regs = (frame word).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,cmpZero16Function,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]
private theorem restrictedDFG (word : BitVec 16) (input : Inputs word) :
    DFGCons input.event.ctx (restrict (frame word) (availOf function (availIn function input.result.ctx) 0 1)) :=
  dfgCons_congr (ctx := input.event.ctx) (fr := frame word) rfl rfl (frame_available word input.result.ctx) input.dfg
private theorem getX (word : BitVec 16) (ctx : Ctx) :
    (restrict (frame word) (availOf function (availIn function ctx) 0 1)).getAs 7 .i16 = .ok word := by
  have same := getAs_congr (fr := frame word)
    (fr' := restrict (frame word) (availOf function (availIn function ctx) 0 1))
    (x := 7) (ty := .i16) (congrFun (frame_available word ctx) 7)
  exact same.trans rfl
private theorem getY (word : BitVec 16) (ctx : Ctx) :
    (restrict (frame word) (availOf function (availIn function ctx) 0 1)).getAs 31 .i16 =
      .ok (BitVec.ofNat 16 0) := by
  have same := getAs_congr (fr := frame word)
    (fr' := restrict (frame word) (availOf function (availIn function ctx) 0 1))
    (x := 31) (ty := .i16) (congrFun (frame_available word ctx) 31)
  exact same.trans rfl
private theorem current (word : BitVec 16) (input : Inputs word) :
    input.record.inst = blockStart function 0 + (1 : Nat) := by
  simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
private theorem guarded (word : BitVec 16) (input : Inputs word) :
    ValuesHeld (fun v => Demanded input.record.output.state v ∧ v ∈ availOf function (availIn function input.result.ctx) 0 1)
      input.event.ctx (frame word) (fun key => regs word (aliasNum input.result.final.alias key)) :=
  input.held.mono (fun _ needed => needed.1)
/-- A complete actual retained Stock.lower comparison and original source step
inhabit fresh result binding, original guarded source transfer and boolean
execution, with dirty upper input bits and sparse original source numbering. -/
theorem stock_cmp_narrow_actual_zero16_eq_complete_source_witness_all_values (word : BitVec 16) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_2215.id ∧
      step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame word,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs word) world (fun ρ' _ =>
          VHolds ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .eq word (0#16))⟩ (ρ' d) ∧ (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → ρ' k = regs word k) ∧
          ValuesHeld (fun v => Demanded record.input v ∧ v ∈ availOf function (availIn function result.ctx) 0 2) event.ctx
            fr' (fun key => ρ' (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs word
  let value : Clif.Val := ⟨.i8,Clif.Sem.bool8 (Clif.Sem.intcc .eq word (0#16))⟩
  let fr' : Clif.Frame := {frame word with regs := (frame word).regs.set 100 value,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame word) Clif.Mem.empty (.icmp .eq .i16 7 31) =
      .ok ([value],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame word,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.icmp .eq .i16 7 31,[value],(frame word).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    · rw [input.results]; rfl
    · rw [input.results]; rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_cmp_narrow_actual_source_values input.run scope dominated input.events input.records
    (bi := 0) (j := 1) (block := function.blocks[0]!) rfl rfl (current word input) input.source input.clif true rfl
    input.typeX input.typeY input.results rfl input.mapped input.recorded input.emitted
    self (restrictedDFG word input) (getX word input.result.ctx) (getY word input.result.ctx) (guarded word input) sourceStep
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,scope,dominated,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,lower,upper,sourceStep,execution⟩
end Backend.Stock.Proof.ScalarCmp.NarrowActualZero16EqAllValuesWitness
