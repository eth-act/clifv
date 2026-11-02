import FV.Backend.Proof.StockCastPair
import FV.Backend.Proof.StockCastSourceValues
import FV.Backend.Proof.LowerValueRelations
namespace Backend.Stock.Proof.ScalarCast.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def instruction (sg : Bool) (pair : Pair) : Clif.Inst := .extend (extendOp sg) pair.toTy 7
private def function (sg : Bool) (pair : Pair) : Clif.Function := {
  name := "stock_extend_source_values"
  sig := {params := [⟨pair.fromTy,.none,.normal⟩],returns := [⟨pair.toTy,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,pair.fromTy)],body := [⟨[100],instruction sg pair⟩],term := .ret [100]}] }
private def built (sg : Bool) (pair : Pair) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function sg pair)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (sg : Bool) (pair : Pair) : Clif.Frame := {
  func := function sg pair,regs := fun x => if x = 7 then some (.ofInt pair.fromTy (-91)) else none,
  slots := [],body := [⟨[100],instruction sg pair⟩],term := .ret [100] }
private def regs (pair : Pair) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+(Clif.Val.ofInt pair.fromTy (-91)).bits.toNat) else 0
private def demand : Array Nat := (Array.replicate 101 0).modify 7 (·+1) |>.modify 100 (·+1)
private def sourceKey (info : IInfo) := (info.clif,info.results)
private def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
private theorem scope (sg : Bool) (pair : Pair) : LowerScope (function sg pair) :=
  lowerScope_of (by cases sg <;> cases pair <;> decide +kernel)
section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private def observedReport (sg : Bool) (pair : Pair) : Option Bool :=
  (Stock.lower (function sg pair)).toOption.map (fun result =>
    decide (aliasNum result.final.alias 192 = 192) && result.blockScans.toList.any (fun event =>
      decide (ctxKey event.ctx = ctxKey (built sg pair).1) && event.output.records.any (fun record =>
        record.inst == (0 : Nat) && decide (record.output.state.demand = demand) &&
        record.output.step.any (fun step => step.decision == .emitted && decide (step.rules.getLast? = some (extendRule sg).id)))))
private theorem observed_false_b8_16 : observedReport false .b8_16 = some true := by decide +kernel
private theorem observed_false_b8_32 : observedReport false .b8_32 = some true := by decide +kernel
private theorem observed_false_b8_64 : observedReport false .b8_64 = some true := by decide +kernel
private theorem observed_false_b16_32 : observedReport false .b16_32 = some true := by decide +kernel
private theorem observed_false_b16_64 : observedReport false .b16_64 = some true := by decide +kernel
private theorem observed_false_b32_64 : observedReport false .b32_64 = some true := by decide +kernel
private theorem observed_true_b8_16 : observedReport true .b8_16 = some true := by decide +kernel
private theorem observed_true_b8_32 : observedReport true .b8_32 = some true := by decide +kernel
private theorem observed_true_b8_64 : observedReport true .b8_64 = some true := by decide +kernel
private theorem observed_true_b16_32 : observedReport true .b16_32 = some true := by decide +kernel
private theorem observed_true_b16_64 : observedReport true .b16_64 = some true := by decide +kernel
private theorem observed_true_b32_64 : observedReport true .b32_64 = some true := by decide +kernel
private theorem observed (sg : Bool) (pair : Pair) : observedReport sg pair = some true := by
  cases sg <;> cases pair
  · exact observed_false_b8_16
  · exact observed_false_b8_32
  · exact observed_false_b8_64
  · exact observed_false_b16_32
  · exact observed_false_b16_64
  · exact observed_false_b32_64
  · exact observed_true_b8_16
  · exact observed_true_b8_32
  · exact observed_true_b8_64
  · exact observed_true_b16_32
  · exact observed_true_b16_64
  · exact observed_true_b32_64
end Runs

private structure Inputs (sg : Bool) (pair : Pair) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function sg pair) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = 0
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (instruction sg pair)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 193 .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (extendRule sg).id
  insts : event.ctx.insts.map sourceKey = (built sg pair).1.insts.map sourceKey
  types : event.ctx.valTy = (built sg pair).1.valTy
  defs : event.ctx.valDef = (built sg pair).1.valDef
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame sg pair)
    (fun k => regs pair (aliasNum result.final.alias k))
private theorem inputs (sg : Bool) (pair : Pair) : Nonempty (Inputs sg pair) := by
  have actual := observed sg pair
  unfold observedReport at actual
  cases run : Stock.lower (function sg pair) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,event,events,ctxEq,record,records,current,demandEq,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some (extendRule sg).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey = some (some (instruction sg pair),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      cases sg <;> cases pair <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (instruction sg pair) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 193 .int) := by
      simp only [Ctx.valueReg?,maps]
      cases sg <;> cases pair <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame sg pair)
        (fun k => regs pair (aliasNum result.final.alias k)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt pair.fromTy (-91)) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          cases sg <;> cases pair <;> rfl
        · dsimp only; rw [alias192]
          cases pair <;> unfold VHolds <;> decide +kernel
      · simp [frame,seven] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,insts,types,defs,held⟩⟩
private theorem dfg_base (sg : Bool) (pair : Pair) : DFGCons (built sg pair).1 (frame sg pair) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : (built sg pair).1.defInst? 7 = none := by cases sg <;> cases pair <;> rfl
      rw [absent] at defined; cases defined
    · simp [frame,seven] at lookup
  · intro x t v typed lookup
    by_cases seven : x = 7
    · subst x
      cases sg <;> cases pair
      all_goals
        change some (.int _) = some t at typed
        cases typed
        cases lookup
        rfl
    · simp [frame,seven] at lookup
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
private theorem dominated (sg : Bool) (pair : Pair) : Dominated (function sg pair) := by
  constructor
  · change ([7,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function] at block
      subst b
      constructor
      · intro j stm statement v member
        cases j <;> simp at statement
        subst stm
        change v ∈ [7] at member
        have equal := List.mem_singleton.mp member
        subst v
        simp [availOf,function,defsBefore,defsFrom]
      · intro v member
        have narrowed : v ∈ [100] := by cases sg <;> cases pair <;> exact member
        have equal := List.mem_singleton.mp narrowed
        subst v
        simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function sg pair) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function sg pair).blocks.length = 1 := rfl
    omega
private theorem frame_available (sg : Bool) (pair : Pair) (ctx : Ctx) :
    (restrict (frame sg pair) (availOf (function sg pair) (availIn (function sg pair) ctx) 0 0)).regs = (frame sg pair).regs := by
  funext x
  by_cases seven : x = 7
  · subst x
    apply restrict_regs_of_mem
    simp [availOf,function,defsBefore,defsFrom]
  · simp [restrict,frame,seven]
/-- Complete actual zero/sign-extension source and retained-record witnesses
cover all six scalar widening pairs, with dirty upper machine bits. -/
theorem stock_lower_extend_source_values_witness (sg : Bool) (pair : Pair) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (d : Nat) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function sg pair) = .ok result ∧ LowerScope (function sg pair) ∧ Dominated (function sg pair) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs pair) ρ' ∧
      VHolds ⟨pair.toTy,extendBits sg pair.toTy.width (Clif.Val.ofInt pair.fromTy (-91)).bits⟩ (ρ' d) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame sg pair,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf (function sg pair) (availIn (function sg pair) result.ctx) 0 1) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := inputs sg pair
  have rawDFG := dfg_transport input.insts input.types input.defs (dfg_base sg pair)
  have sameFrame := frame_available sg pair input.result.ctx
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := frame sg pair)
    (fr' := restrict (frame sg pair) (availOf (function sg pair) (availIn (function sg pair) input.result.ctx) 0 0))
    rfl rfl sameFrame rawDFG
  have getX : (restrict (frame sg pair) (availOf (function sg pair) (availIn (function sg pair) input.result.ctx) 0 0)).regs 7 =
      some (.ofInt pair.fromTy (-91)) := by rw [sameFrame]; rfl
  have guarded := input.held.mono (fun v (h : Demanded input.record.output.state v ∧
      v ∈ availOf (function sg pair) (availIn (function sg pair) input.result.ctx) 0 0) => h.1)
  let val : Clif.Val := ⟨pair.toTy,extendBits sg pair.toTy.width (Clif.Val.ofInt pair.fromTy (-91)).bits⟩
  let fr' : Clif.Frame := {frame sg pair with regs := (frame sg pair).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame sg pair) Clif.Mem.empty (instruction sg pair) =
      .ok ([val],Clif.Mem.empty) := by cases sg <;> cases pair <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame sg pair,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,instruction sg pair,[val],(frame sg pair).regs.set 100 val,[],input.source,input.clif,
      by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have block : (function sg pair).blocks[0]? = some ((function sg pair).blocks[0]!) := rfl
  have statement : ((function sg pair).blocks[0]!).body[0]? = some (⟨[100],instruction sg pair⟩ : Clif.Stmt) := rfl
  have current : input.record.inst = blockStart (function sg pair) 0 + 0 := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨d,ρ',output,bounds,execution,value,kept,post⟩ := stock_lower_extend_available_source input.run
    (scope sg pair) (dominated sg pair) input.events input.records block statement current sg
    input.source input.clif input.results rfl input.mapped input.recorded input.emitted input.selectedId
    self restrictedDFG guarded getX sourceStep
  exact ⟨input.result,input.event,input.record,d,ρ',fr',input.run,scope sg pair,dominated sg pair,input.events,input.records,
    bounds,execution,value,sourceStep,post⟩

end Backend.Stock.Proof.ScalarCast.Witness
