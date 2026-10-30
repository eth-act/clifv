import FV.Backend.Proof.StockSelectOriginalSourceValues
import FV.Backend.Proof.LowerSim
import FV.Backend.Proof.StockSelectComparisonSourceSetup
namespace Backend.Stock.Proof.ScalarSelect.ComparisonSourceWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem getter {fr : Clif.Frame} {x : Nat} {ty : Clif.Ty} {bits : BitVec ty.width}
    (read : fr.regs x = some ⟨ty,bits⟩) : fr.getAs x ty = .ok bits := by
  unfold Clif.Frame.getAs Clif.Frame.get
  rw [read]
  simp [Clif.Res.ofOption]
private theorem dirty_word (ty : Clif.Ty) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (word : BitVec ty.width) : (BitVec.ofNat 128 (2^100+word.toNat)).setWidth ty.width = word := by
  have bound : ty.width ≤ 128 := by omega
  have high : 2^100 % 2^ty.width = 0 := by rcases width with h | h | h | h <;> rw [h] <;> decide +kernel
  rw [BitVec.setWidth_ofNat_of_le bound]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.add_mod,high,Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
private theorem dfg_transport {a b : Ctx} {fr : Clif.Frame}
    (insts : a.insts.map minmaxSourceKey = b.insts.map minmaxSourceKey)
    (types : a.valTy = b.valTy) (defs : a.valDef = b.valDef) (dfg : DFGCons b fr) : DFGCons a fr := by
  constructor
  · intro x j info cl v defined found original pure lookup
    have view : (b.insts[j]?).map minmaxSourceKey = some (minmaxSourceKey info) := by
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
private structure Inputs (p : Case) (a b : BitVec p.cty.width) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function p) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = index p
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.select p.ty (conditionKey p) 63 95)
  results : info.results = [102]
  mapped : event.ctx.valueReg? 102 = some (.vreg (if p.extended then 198 else 197) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some rule_lower_2267.id
  dfg : DFGCons event.ctx (frame p a b)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame p a b)
    (fun key => registers p a b (aliasNum result.final.alias key))
private theorem inputs (p : Case) (a b : BitVec p.cty.width) : Nonempty (Inputs p a b) := by
  have actual := ComparisonDriver.stock_select_comparison_driver_observed p.cty p.ty p.extended p.comparisonWidth p.width p.cint p.int
  unfold ComparisonDriver.Observed at actual
  cases run : Stock.lower (function p) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq,
      List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨aliasA,aliasB,aliasX,aliasY,event,events,ctxEq,record,records,current,zero100,zero101,stepData⟩ := actual
    simp only [minmaxCtxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_2267.id)
    have keyAt : (event.ctx.insts[record.inst]?).map minmaxSourceKey =
        some (some (.select p.ty (conditionKey p) 63 95),[102]) := by
      rw [← Array.getElem?_map,insts,current,Array.getElem?_map]
      exact (stock_select_comparison_source_setup p).source
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.select p.ty (conditionKey p) 63 95) at clif
    change info.results = [102] at results
    have mapped : event.ctx.valueReg? 102 = some (.vreg (if p.extended then 198 else 197) .int) := by
      simpa [Ctx.valueReg?,maps] using (stock_select_comparison_source_setup p).mapped 102 (by simp)
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame p a b)
        (fun key => registers p a b (aliasNum result.final.alias key)) := by
      intro x needed value lookup
      by_cases ha : x = 7
      · subst x
        simp only [frame,ite_true,Option.some.injEq] at lookup
        subst value
        refine ⟨192,?_,?_⟩
        · simpa [Ctx.valueReg?,maps] using (stock_select_comparison_source_setup p).mapped 7 (by simp)
        · dsimp only
          rw [aliasA]
          exact dirty_word p.cty p.comparisonWidth a
      · by_cases hb : x = 31
        · subst x
          simp [frame] at lookup
          subst value
          refine ⟨193,?_,?_⟩
          · simpa [Ctx.valueReg?,maps] using (stock_select_comparison_source_setup p).mapped 31 (by simp)
          · dsimp only
            rw [aliasB]
            exact dirty_word p.cty p.comparisonWidth b
        · by_cases hx : x = 63
          · subst x
            simp [frame] at lookup
            subst value
            refine ⟨194,?_,?_⟩
            · simpa [Ctx.valueReg?,maps] using (stock_select_comparison_source_setup p).mapped 63 (by simp)
            · dsimp only
              rw [aliasX]
              change (BitVec.ofNat 128 (2^100+7)).setWidth p.ty.width = BitVec.ofNat p.ty.width 7
              rcases p.width with h | h | h | h <;> rw [h] <;> decide +kernel
          · by_cases hy : x = 95
            · subst x
              simp [frame] at lookup
              subst value
              refine ⟨195,?_,?_⟩
              · simpa [Ctx.valueReg?,maps] using (stock_select_comparison_source_setup p).mapped 95 (by simp)
              · dsimp only
                rw [aliasY]
                change (BitVec.ofNat 128 (2^100+9)).setWidth p.ty.width = BitVec.ofNat p.ty.width 9
                rcases p.width with h | h | h | h <;> rw [h] <;> decide +kernel
            · by_cases h100 : x = 100
              · subst x; exact False.elim (needed zero100)
              · by_cases h101 : x = 101
                · subst x; exact False.elim (needed zero101)
                · simp [frame,ha,hb,hx,hy,h100,h101] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,dfg_transport insts types defs ((stock_select_comparison_source_setup p).dfg a b),held⟩⟩
private theorem dominated (p : Case) : Dominated (function p) := by
  constructor
  · cases extended : p.extended
    · simpa [valueDefs,function,ComparisonDriver.function,extended] using (show ([7,31,63,95,100,102] : List Nat).Nodup from by decide +kernel)
    · simpa [valueDefs,function,ComparisonDriver.function,extended] using (show ([7,31,63,95,100,101,102] : List Nat).Nodup from by decide +kernel)
  · intro ctx ranges st build bi block found
    cases bi with
    | zero =>
      simp [function,ComparisonDriver.function] at found
      subst block
      constructor
      · intro j stmt statement x member
        cases extended : p.extended
        all_goals rcases j with _ | _ | _ | j
        all_goals simp [function,ComparisonDriver.function,extended] at statement
        all_goals subst stmt
        all_goals simp only [Backend.Proof.Driver.instArgs,List.mem_cons,List.not_mem_nil,or_false] at member
        all_goals repeat' first | (subst x) | (rcases member with member | member)
        all_goals simp [availOf,function,ComparisonDriver.function,extended,defsBefore,defsFrom]
      · intro x member
        have members : x ∈ [102] := by
          rcases p with ⟨cty,ty,extended,hc,ht,ci,ti⟩
          cases cty <;> cases ty <;> cases extended <;> simp [Clif.Ty.width] at hc ht ci ti <;> exact member
        have equal : x = 102 := List.mem_singleton.mp members
        subst x
        cases extended : p.extended <;> simp [availOf,function,ComparisonDriver.function,extended,defsBefore,defsFrom]
    | succ bi => simp [function,ComparisonDriver.function] at found
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function p) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function p).blocks.length = 1 := rfl
    omega
private theorem frame_available (p : Case) (a b : BitVec p.cty.width) (ctx : Ctx) :
    (restrict (frame p a b) (availOf (function p) (availIn (function p) ctx) 0 (index p))).regs = (frame p a b).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31 ∨ x = 63 ∨ x = 95 ∨ x = 100 ∨ x = 101
  · rcases present with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (solve | apply restrict_regs_of_mem; cases extended : p.extended <;>
          simp [availOf,function,ComparisonDriver.function,index,extended,defsBefore,defsFrom])
      | (cases extended : p.extended
         · simp [restrict,frame,extended]
         · apply restrict_regs_of_mem; simp [availOf,function,ComparisonDriver.function,index,extended,defsBefore,defsFrom])
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2.1,present.2.2.1,present.2.2.2.1,present.2.2.2.2.1,present.2.2.2.2.2]
private theorem restrictedDFG (p : Case) (a b : BitVec p.cty.width) (input : Inputs p a b) :
    DFGCons input.event.ctx (restrict (frame p a b) (availOf (function p) (availIn (function p) input.result.ctx) 0 (index p))) :=
  dfgCons_congr (ctx := input.event.ctx) (fr := frame p a b) rfl rfl (frame_available p a b input.result.ctx) input.dfg
private theorem condition_read (p : Case) (a b : BitVec p.cty.width) :
    (frame p a b).regs (conditionKey p) = some ⟨conditionTy p,conditionBits p a b⟩ := by
  rcases p with ⟨cty,ty,extended,hc,ht,ci,ti⟩
  cases extended
  all_goals dsimp only [frame,conditionKey,conditionTy,conditionBits,Case.cty,Case.ty,Case.extended]
  all_goals generalize Clif.Sem.intcc .ult a b = result
  all_goals cases result <;> rfl
/-- All32 scalar width/form families and every original comparison operand pair
inhabit complete retained original select/source-step execution. The original
icmp/uextend condition is undemanded, and the selected values are distinct7/9.
Sparse source IDs, dirty machine bits, actual aliases, memory and full guarded
post-frame are established from actual complete Stock.lower runs. -/
theorem stock_select_comparison_complete_source_witness (p : Case) (a b : BitVec p.cty.width) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower (function p) = .ok result ∧ LowerScope (function p) ∧ Dominated (function p) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ record.output.step = some step ∧
      step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_2267.id ∧
      step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame p a b,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (registers p a b) world (fun final _ =>
          VHolds ⟨p.ty,Clif.Sem.select (conditionBits p a b) 7 9⟩ (final d) ∧
          (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → final key = registers p a b key) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf (function p) (availIn (function p) result.ctx) 0 (index p+1))
            event.ctx fr' (fun key => final (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs p a b
  let value : Clif.Val := ⟨p.ty,Clif.Sem.select (conditionBits p a b) 7 9⟩
  let fr' : Clif.Frame := {frame p a b with regs := (frame p a b).regs.set 102 value,body := []}
  have rawGetC : (frame p a b).getAs (conditionKey p) (conditionTy p) = .ok (conditionBits p a b) :=
    getter (condition_read p a b)
  have rawGetX : (frame p a b).getAs 63 p.ty = .ok 7 := getter (by simp [frame])
  have rawGetY : (frame p a b).getAs 95 p.ty = .ok 9 := getter (by simp [frame])
  have getC := (getAs_congr (x := conditionKey p) (ty := conditionTy p) (congrFun (frame_available p a b input.result.ctx) (conditionKey p))).trans rawGetC
  have getX := (getAs_congr (x := 63) (ty := p.ty) (congrFun (frame_available p a b input.result.ctx) 63)).trans rawGetX
  have getY := (getAs_congr (x := 95) (ty := p.ty) (congrFun (frame_available p a b input.result.ctx) 95)).trans rawGetY
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame p a b) Clif.Mem.empty
      (.select p.ty (conditionKey p) 63 95) = .ok ([value],Clif.Mem.empty) := by
    simp [instOutcome,Clif.evalInst,Clif.Frame.get,getAs_ok rawGetC,rawGetX,rawGetY,value]
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame p a b,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.select p.ty (conditionKey p) 63 95,[value],(frame p a b).regs.set 102 value,[],
      input.source,input.clif,?_,evaluated,?_,rfl⟩
    · rw [input.results]; rfl
    · rw [input.results]; rfl
  have guarded : ValuesHeld (fun v => Demanded input.record.output.state v ∧ v ∈ availOf (function p) (availIn (function p) input.result.ctx) 0 (index p))
      input.event.ctx (frame p a b) (fun key => registers p a b (aliasNum input.result.final.alias key)) :=
    input.held.mono (fun _ needed => needed.1)
  have current : input.record.inst = blockStart (function p) 0 + index p := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have statement : ((function p).blocks[0]!.body[index p]?) = some ⟨[102],.select p.ty (conditionKey p) 63 95⟩ := by
    cases extended : p.extended <;> simp [function,ComparisonDriver.function,index,conditionKey,extended]
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_select_source_values input.run (stock_select_comparison_source_setup p).scope (dominated p)
    input.events input.records (bi := 0) (j := index p) (block := (function p).blocks[0]!) rfl statement current input.source input.clif
    input.results rfl input.mapped input.recorded input.emitted
    self (restrictedDFG p a b input) getC getX getY guarded sourceStep
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,(stock_select_comparison_source_setup p).scope,dominated p,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,lower,upper,sourceStep,execution⟩
end Backend.Stock.Proof.ScalarSelect.ComparisonSourceWitness
