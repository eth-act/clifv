import FV.Backend.Proof.StockReduceSourceValues
import FV.Backend.Proof.StockCastWitness
import FV.Backend.Proof.LowerValueRelations
namespace Backend.Stock.Proof.ScalarCast.Reduce.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open ScalarCast.Witness (Pair)
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def rootIndex (aliased : Bool) : Nat := if aliased then 1 else 0
private def instruction (pair : Pair) : Clif.Inst := .ireduce pair.fromTy 7
private def function (pair : Pair) (aliased : Bool) : Clif.Function := {
  name := "stock_reduce_source_values"
  sig := {params := (if aliased then [] else [⟨pair.toTy,.none,.normal⟩]),returns := [⟨pair.fromTy,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := (if aliased then [] else [(7,pair.toTy)]),body :=
    (if aliased then [⟨[7],.iconst pair.toTy (BitVec.ofInt pair.toTy.width (-91))⟩] else []) ++ [⟨[100],instruction pair⟩],term := .ret [100]}] }
private def built (pair : Pair) (aliased : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function pair aliased)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (pair : Pair) (aliased : Bool) : Clif.Frame := {
  func := function pair aliased,regs := fun x => if x = 7 then some (.ofInt pair.toTy (-91)) else none,
  slots := [],body := [⟨[100],instruction pair⟩],term := .ret [100] }
private def regs (pair : Pair) (aliased : Bool) (n : Nat) : CV :=
  if n = (if aliased then 194 else 192) then BitVec.ofNat 128 (2^100+(Clif.Val.ofInt pair.toTy (-91)).bits.toNat) else 0
private def demand : Array Nat := (Array.replicate 101 0).modify 7 (·+1) |>.modify 100 (·+1)
private def sourceKey (info : IInfo) := (info.clif,info.results)
private def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
private theorem scope (pair : Pair) (aliased : Bool) : LowerScope (function pair aliased) :=
  lowerScope_of (by cases pair <;> cases aliased <;> decide +kernel)
section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private def observedReport (pair : Pair) (aliased : Bool) : Option Bool :=
  (Stock.lower (function pair aliased)).toOption.map (fun result =>
    decide ((result.final.alias[193]?).join = some 192) &&
    decide (aliasNum result.final.alias 192 = if aliased then 194 else 192) && result.blockScans.toList.any (fun event =>
      decide (ctxKey event.ctx = ctxKey (built pair aliased).1) && event.output.records.any (fun record =>
        record.inst == rootIndex aliased && decide (record.output.state.demand = demand) &&
        record.output.step.any (fun step => step.decision == .emitted && decide (step.rules.getLast? = some rule_lower_2146.id)))))
private theorem observed_b8_16_false : observedReport .b8_16 false = some true := by decide +kernel
private theorem observed_b8_16_true : observedReport .b8_16 true = some true := by decide +kernel
private theorem observed_b8_32_false : observedReport .b8_32 false = some true := by decide +kernel
private theorem observed_b8_32_true : observedReport .b8_32 true = some true := by decide +kernel
private theorem observed_b8_64_false : observedReport .b8_64 false = some true := by decide +kernel
private theorem observed_b8_64_true : observedReport .b8_64 true = some true := by decide +kernel
private theorem observed_b16_32_false : observedReport .b16_32 false = some true := by decide +kernel
private theorem observed_b16_32_true : observedReport .b16_32 true = some true := by decide +kernel
private theorem observed_b16_64_false : observedReport .b16_64 false = some true := by decide +kernel
private theorem observed_b16_64_true : observedReport .b16_64 true = some true := by decide +kernel
private theorem observed_b32_64_false : observedReport .b32_64 false = some true := by decide +kernel
private theorem observed_b32_64_true : observedReport .b32_64 true = some true := by decide +kernel
private theorem observed (pair : Pair) (aliased : Bool) : observedReport pair aliased = some true := by
  cases pair <;> cases aliased
  · exact observed_b8_16_false
  · exact observed_b8_16_true
  · exact observed_b8_32_false
  · exact observed_b8_32_true
  · exact observed_b8_64_false
  · exact observed_b8_64_true
  · exact observed_b16_32_false
  · exact observed_b16_32_true
  · exact observed_b16_64_false
  · exact observed_b16_64_true
  · exact observed_b32_64_false
  · exact observed_b32_64_true
end Runs
private structure Inputs (pair : Pair) (aliased : Bool) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function pair aliased) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = rootIndex aliased
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (instruction pair)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 193 .int)
  sourceMapped : event.ctx.valueReg? 7 = some (.vreg 192 .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some rule_lower_2146.id
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame pair aliased)
    (fun k => regs pair aliased (aliasNum result.final.alias k))
private theorem inputs (pair : Pair) (aliased : Bool) : Nonempty (Inputs pair aliased) := by
  have actual := observed pair aliased
  unfold observedReport at actual
  cases run : Stock.lower (function pair aliased) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨edge193,alias192,event,events,ctxEq,record,records,current,demandEq,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_2146.id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey = some (some (instruction pair),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      cases pair <;> cases aliased <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (instruction pair) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 193 .int) := by
      simp only [Ctx.valueReg?,maps]
      cases pair <;> cases aliased <;> rfl
    have sourceMapped : event.ctx.valueReg? 7 = some (.vreg 192 .int) := by
      simp only [Ctx.valueReg?,maps]
      cases pair <;> cases aliased <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame pair aliased)
        (fun k => regs pair aliased (aliasNum result.final.alias k)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt pair.toTy (-91)) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          cases pair <;> cases aliased <;> rfl
        · dsimp only; rw [alias192]
          cases pair <;> cases aliased <;> unfold VHolds <;> decide +kernel
      · simp [frame,seven] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,sourceMapped,
      recorded,emitted,selectedId,held⟩⟩
private theorem dominated (pair : Pair) (aliased : Bool) : Dominated (function pair aliased) := by
  constructor
  · cases aliased <;> change ([7,100] : List Nat).Nodup <;> decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function] at block
      subst b
      constructor
      · intro j stm statement v member
        cases aliased
        · cases j <;> simp at statement
          subst stm
          change v ∈ [7] at member
          have equal := List.mem_singleton.mp member
          subst v
          simp [availOf,function,defsBefore,defsFrom]
        · cases j
          · simp at statement; subst stm; cases member
          · rename_i j
            cases j <;> simp at statement
            subst stm
            change v ∈ [7] at member
            have equal := List.mem_singleton.mp member
            subst v
            simp [availOf,function,defsBefore,defsFrom]
      · intro v member
        have narrowed : v ∈ [100] := by cases pair <;> cases aliased <;> exact member
        have equal := List.mem_singleton.mp narrowed
        subst v
        cases aliased <;> simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function pair aliased) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function pair aliased).blocks.length = 1 := rfl
    omega
private theorem frame_available (pair : Pair) (aliased : Bool) (ctx : Ctx) :
    (restrict (frame pair aliased) (availOf (function pair aliased) (availIn (function pair aliased) ctx) 0
      (rootIndex aliased))).regs = (frame pair aliased).regs := by
  funext x
  by_cases seven : x = 7
  · subst x
    apply restrict_regs_of_mem
    cases aliased <;> simp [availOf,function,rootIndex,defsBefore,defsFrom]
  · simp [restrict,frame,seven]
/-- Complete original reduction source/record witnesses cover every scalar
narrowing pair. The second form reads an earlier producer's fresh endpoint,
while its original source vreg is deliberately unmaterialized. -/
theorem stock_lower_reduce_source_values_witness (pair : Pair) (aliased : Bool) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (fr' : Clif.Frame),
      Stock.lower (function pair aliased) = .ok result ∧ LowerScope (function pair aliased) ∧ Dominated (function pair aliased) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ record.output.emitted = #[] ∧
      aliasNum result.final.alias 193 = aliasNum result.final.alias 192 ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs pair aliased) (regs pair aliased) ∧
      VHolds ⟨pair.fromTy,Clif.Sem.ireduce pair.fromTy.width (Clif.Val.ofInt pair.toTy (-91)).bits⟩
        (regs pair aliased (aliasNum result.final.alias 193)) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame pair aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf (function pair aliased) (availIn (function pair aliased) result.ctx) 0 (rootIndex aliased+1)) event.ctx fr'
        (fun k => regs pair aliased (aliasNum result.final.alias k)) ∧
      (aliased = true → regs pair aliased 192 = 0) := by
  obtain ⟨input⟩ := inputs pair aliased
  have sameFrame := frame_available pair aliased input.result.ctx
  have getX : (restrict (frame pair aliased) (availOf (function pair aliased) (availIn (function pair aliased) input.result.ctx) 0
      (rootIndex aliased))).regs 7 = some (.ofInt pair.toTy (-91)) := by rw [sameFrame]; rfl
  have guarded := input.held.mono (fun v (h : Demanded input.record.output.state v ∧
      v ∈ availOf (function pair aliased) (availIn (function pair aliased) input.result.ctx) 0 (rootIndex aliased)) => h.1)
  let val : Clif.Val := ⟨pair.fromTy,Clif.Sem.ireduce pair.fromTy.width (Clif.Val.ofInt pair.toTy (-91)).bits⟩
  let fr' : Clif.Frame := {frame pair aliased with regs := (frame pair aliased).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame pair aliased) Clif.Mem.empty (instruction pair) =
      .ok ([val],Clif.Mem.empty) := by cases pair <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame pair aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,instruction pair,[val],(frame pair aliased).regs.set 100 val,[],input.source,input.clif,
      by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have block : (function pair aliased).blocks[0]? = some ((function pair aliased).blocks[0]!) := rfl
  have statement : ((function pair aliased).blocks[0]!).body[rootIndex aliased]? = some (⟨[100],instruction pair⟩ : Clif.Stmt) := by
    cases aliased <;> rfl
  have current : input.record.inst = blockStart (function pair aliased) 0 + rootIndex aliased := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  obtain ⟨nx,sourceMap,output,code,endpoints,memEq,execution,value,post⟩ := stock_lower_reduce_available_source input.run
    (scope pair aliased) (dominated pair aliased) input.events input.records block statement current input.source input.clif
    input.results rfl input.mapped input.recorded input.emitted input.selectedId guarded getX sourceStep (fun _ => True) ispec
  have nxEq : nx = 192 := by
    have regsEq := Option.some.inj (sourceMap.symm.trans input.sourceMapped)
    exact (Reg.vreg.inj regsEq).1
  subst nx
  exact ⟨input.result,input.event,input.record,fr',input.run,scope pair aliased,dominated pair aliased,input.events,input.records,
    code,endpoints,execution,value,sourceStep,post,fun yes => by subst aliased; rfl⟩

end Backend.Stock.Proof.ScalarCast.Reduce.Witness
