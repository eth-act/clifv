import FV.Backend.Proof.StockMinMaxWideBothConstantDriverRuns
import FV.Backend.Proof.StockMinMaxWideSourceReads
import FV.Backend.Proof.LowerValueRelations
namespace Backend.Stock.Proof.ScalarSelect.WideBothConstantWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarSelect Backend.Stock.Proof.ScalarSelect.MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Fixture parameters cover all four operations and both widths with two
materialized constants and their actual final aliases. -/
structure Case where
  unsigned : Bool
  maximum : Bool
  wide : Bool
private def ty (p : Case) := wideMinmaxTy p.wide
private def literal (_p : Case) : Nat := 3
private def x (_p : Case) : Nat := 7
private def y (_p : Case) : Nat := 31
private def function (p : Case) := wideBothConstantFunction p.unsigned p.maximum p.wide
private def built (p : Case) := wideBothConstantBuilt p.unsigned p.maximum p.wide
private def frame (p : Case) : Clif.Frame := {
  func := function p
  regs := fun key => if key = 31 then some (.ofInt (ty p) 65537) else
    if key = 7 then some (.ofInt (ty p) 3) else none
  slots := [],body := [⟨[100],.binary (minmaxOperation p.unsigned p.maximum) (ty p) 7 31⟩],term := .ret [100] }
private def regs (p : Case) (n : Nat) : CV :=
  if n = wideBothConstantTargetX p.wide then BitVec.ofNat 128 (2^100+3)
  else if n = wideBothConstantTargetY p.wide then BitVec.ofNat 128 (2^100+65537)
  else 0
private theorem scope (p : Case) : LowerScope (function p) := by
  apply lowerScope_of
  rcases p with ⟨u,m,w⟩
  cases u <;> cases m <;> cases w <;> decide +kernel
private theorem defined (p : Case) : (built p).1.defInst? 7 = some 0 := by
  rcases p with ⟨u,m,w⟩
  cases u <;> cases m <;> cases w <;> rfl
private theorem definedY (p : Case) : (built p).1.defInst? 31 = some 1 := by
  rcases p with ⟨u,m,w⟩
  cases u <;> cases m <;> cases w <;> rfl
private theorem typed (p : Case) (key : Nat) (present : key = 31 ∨ key = 7) :
    (built p).1.valueType? key = some (.int (ty p).width) := by
  rcases present with rfl | rfl
  all_goals rcases p with ⟨u,m,w⟩
  all_goals cases u <;> cases m <;> cases w <;> rfl
private theorem constant (p : Case) :
    ((built p).1.insts[0]?).map minmaxSourceKey =
      some (some (.iconst (ty p) (BitVec.ofNat (ty p).width (literal p))),[7]) := by
  rcases p with ⟨u,m,w⟩
  cases u <;> cases m <;> cases w <;> rfl
private theorem dfg_base (p : Case) : DFGCons (built p).1 (frame p) := by
  constructor
  · intro key j info cl value defn found original pure lookup
    by_cases first : key = 7
    · subst key
      rw [defined p] at defn
      cases defn
      have metadata : ((built p).1.insts[0]?).map minmaxSourceKey =
          some (some (.iconst (ty p) (BitVec.ofNat (ty p).width 3)),[7]) := by
        rcases p with ⟨u,m,w⟩
        cases u <;> cases m <;> cases w <;> rfl
      rw [found] at metadata
      have pair := Option.some.inj metadata
      have clifEq := congrArg Prod.fst pair
      have resultsEq := congrArg Prod.snd pair
      change info.clif = some (.iconst (ty p) (BitVec.ofNat (ty p).width 3)) at clifEq
      change info.results = [7] at resultsEq
      have clEq := Option.some.inj (original.symm.trans clifEq)
      subst cl
      change some (.ofInt (ty p) 3) = some value at lookup
      cases lookup
      refine ⟨[.ofInt (ty p) 3],?_,?_⟩
      · intro cm
        rcases p with ⟨u,m,w⟩
        cases w <;> rfl
      · rw [resultsEq]
        rfl
    · by_cases second : key = 31
      · subst key
        rw [definedY p] at defn
        cases defn
        have metadata : ((built p).1.insts[1]?).map minmaxSourceKey =
            some (some (.iconst (ty p) (BitVec.ofNat (ty p).width 65537)),[31]) := by
          rcases p with ⟨u,m,w⟩
          cases u <;> cases m <;> cases w <;> rfl
        rw [found] at metadata
        have pair := Option.some.inj metadata
        have clifEq := congrArg Prod.fst pair
        have resultsEq := congrArg Prod.snd pair
        change info.clif = some (.iconst (ty p) (BitVec.ofNat (ty p).width 65537)) at clifEq
        change info.results = [31] at resultsEq
        have clEq := Option.some.inj (original.symm.trans clifEq)
        subst cl
        change some (.ofInt (ty p) 65537) = some value at lookup
        cases lookup
        refine ⟨[.ofInt (ty p) 65537],?_,?_⟩
        · intro cm
          rcases p with ⟨u,m,w⟩
          cases w <;> rfl
        · rw [resultsEq]
          rfl
      · simp [frame,first,second] at lookup
  · intro key t value typeEq lookup
    by_cases present : key = 31 ∨ key = 7
    · have typeKey := typed p key present
      rw [typeKey] at typeEq
      cases typeEq
      rcases present with rfl | rfl
      all_goals cases lookup
      all_goals rcases p with ⟨u,m,w⟩
      all_goals cases w <;> rfl
    · simp only [not_or] at present
      simp [frame,present.1,present.2] at lookup
private theorem dfg_transport {a b : Ctx} {fr : Clif.Frame}
    (insts : a.insts.map minmaxSourceKey = b.insts.map minmaxSourceKey)
    (types : a.valTy = b.valTy) (defs : a.valDef = b.valDef) (dfg : DFGCons b fr) : DFGCons a fr := by
  constructor
  · intro key j info cl value defn found original pure lookup
    have view : (b.insts[j]?).map minmaxSourceKey = some (minmaxSourceKey info) := by
      rw [← Array.getElem?_map,← insts,Array.getElem?_map,found]; rfl
    obtain ⟨info',found',same⟩ := Option.map_eq_some_iff.mp view
    have clifEq := congrArg Prod.fst same
    have resultsEq := congrArg Prod.snd same
    change info'.clif = info.clif at clifEq
    change info'.results = info.results at resultsEq
    obtain ⟨vals,evaluated,written⟩ := dfg.1 key j info' cl value
      (by simpa only [Ctx.defInst?,defs] using defn) found' (clifEq.trans original) pure lookup
    exact ⟨vals,evaluated,by rw [← resultsEq]; exact written⟩
  · simpa only [FrameTyped,Ctx.valueType?,types] using dfg.2
private structure Inputs (p : Case)  where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function p) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = 2
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p))
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int)
  typeX : event.ctx.valueType? (x p) = some (.int (ty p).width)
  typeY : event.ctx.valueType? (y p) = some (.int (ty p).width)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (minmaxRule p.unsigned p.maximum).id
  dfg : DFGCons event.ctx (frame p)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame p)
    (fun k => regs p (aliasNum result.final.alias k))
private theorem inputs (p : Case)  : Nonempty (Inputs p) := by
  have actual := stock_minmax_wide_both_constant_driver_observed p.unsigned p.maximum p.wide
  unfold wideBothConstantObserved at actual
  change (Stock.lower (function p)).toOption.map _ = some true at actual
  cases run : Stock.lower (function p) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    change (Stock.lower (function p)).toOption.map _ = some true at actual
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,stepData⟩ := actual
    simp only [minmaxCtxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some (minmaxRule p.unsigned p.maximum).id)
    have keyAt : (event.ctx.insts[record.inst]?).map minmaxSourceKey =
        some (some (.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p)),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      rcases p with ⟨u,m,w⟩
      cases u <;> cases m <;> cases w <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p)) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases p with ⟨u,m,w⟩
      cases u <;> cases m <;> cases w <;> rfl
    have typeX : event.ctx.valueType? (x p) = some (.int (ty p).width) := by
      simp only [Ctx.valueType?,types]
      rcases p with ⟨u,m,w⟩
      cases u <;> cases m <;> cases w <;> rfl
    have typeY : event.ctx.valueType? (y p) = some (.int (ty p).width) := by
      simp only [Ctx.valueType?,types]
      rcases p with ⟨u,m,w⟩
      cases u <;> cases m <;> cases w <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame p)
        (fun n => regs p (aliasNum result.final.alias n)) := by
      intro key needed value lookup
      by_cases second : key = 31
      · subst key
        change some (.ofInt (ty p) 65537) = some value at lookup
        cases lookup
        refine ⟨193,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rcases p with ⟨u,m,w⟩
          cases u <;> cases m <;> cases w <;> rfl
        · change (regs p (aliasNum result.final.alias 193)).setWidth (ty p).width = BitVec.ofNat (ty p).width 65537
          rw [alias193]
          rcases p with ⟨u,m,w⟩
          cases w <;> dsimp [regs,ty,wideBothConstantTargetX,wideBothConstantTargetY,wideMinmaxTy] <;> decide +kernel
      · by_cases first : key = 7
        · subst key
          change some (.ofInt (ty p) 3) = some value at lookup
          cases lookup
          refine ⟨192,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            rcases p with ⟨u,m,w⟩
            cases u <;> cases m <;> cases w <;> rfl
          · change (regs p (aliasNum result.final.alias 192)).setWidth (ty p).width = BitVec.ofNat (ty p).width 3
            rw [alias192]
            rcases p with ⟨u,m,w⟩
            cases w <;> dsimp [regs,ty,wideBothConstantTargetX,wideBothConstantTargetY,wideMinmaxTy] <;> decide +kernel
        · simp [frame,second,first] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,typeX,typeY,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base p),held⟩⟩
private theorem dominated (p : Case) : Dominated (function p) := by
  constructor
  · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function,wideBothConstantFunction] at block
      subst b
      constructor
      · intro j stm statement key member
        cases j with
        | zero => simp at statement; subst stm; change key ∈ ([] : List Nat) at member; cases member
        | succ j =>
          cases j with
          | zero => simp at statement; subst stm; change key ∈ ([] : List Nat) at member; cases member
          | succ j =>
            cases j with
            | zero =>
              simp at statement
              subst stm
              change key ∈ [7,31] at member
              simp only [List.mem_cons,List.not_mem_nil,or_false] at member
              rcases member with rfl | rfl <;> simp [availOf,function,wideBothConstantFunction,defsBefore,defsFrom]
            | succ j => simp at statement
      · intro key member
        have present : key ∈ [100] := by rcases p with ⟨u,m,w⟩; cases w <;> exact member
        have equal := List.mem_singleton.mp present
        subst key
        simp [availOf,function,wideBothConstantFunction,defsBefore,defsFrom]
    | succ bi => simp [function,wideBothConstantFunction] at block
  · intro ctx ranges st build tl key available notLocal other member
    have bound := (inFix_fixOk (f := function p) (ctx := ctx) (gn := id)).cand tl key available
    have length : (function p).blocks.length = 1 := rfl
    omega
private theorem frame_available (p : Case)  (ctx : Ctx) :
    (restrict (frame p) (availOf (function p) (availIn (function p) ctx) 0 2)).regs = (frame p).regs := by
  funext key
  by_cases present : key = 31 ∨ key = 7
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,wideBothConstantFunction,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]
private theorem get_parameter (p : Case)  (ctx : Ctx) :
    (restrict (frame p) (availOf (function p) (availIn (function p) ctx) 0 2)).getAs 31 (ty p) = .ok (BitVec.ofNat (ty p).width 65537) := by
  have same := getAs_congr (fr := frame p)
    (fr' := restrict (frame p) (availOf (function p) (availIn (function p) ctx) 0 2))
    (x := 31) (ty := ty p) (congrFun (frame_available p ctx) 31)
  rcases p with ⟨u,m,w⟩
  cases w <;> exact same.trans rfl
private theorem get_constant (p : Case)  (ctx : Ctx) :
    (restrict (frame p) (availOf (function p) (availIn (function p) ctx) 0 2)).getAs 7 (ty p) =
      .ok (BitVec.ofNat (ty p).width (literal p)) := by
  have same := getAs_congr (fr := frame p)
    (fr' := restrict (frame p) (availOf (function p) (availIn (function p) ctx) 0 2))
    (x := 7) (ty := ty p) (congrFun (frame_available p ctx) 7)
  rcases p with ⟨u,m,w⟩
  cases w <;> exact same.trans rfl
private def first (p : Case) := BitVec.ofNat (ty p).width 3
private def second (p : Case) := BitVec.ofNat (ty p).width 65537
/-- Complete original Stock.lower/retained/source-step witnesses for all8
both-constant forms, with dirty upper bits and the
actual width/encoding-dependent final aliases. -/
theorem stock_minmax_wide_both_constant_complete_source_witness (p : Case)  :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower (function p) = .ok result ∧ LowerScope (function p) ∧ Dominated (function p) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (minmaxRule p.unsigned p.maximum).id ∧
      step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame p,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs p) world
        (fun final _ => VHolds ⟨ty p,Clif.Sem.binary (minmaxOperation p.unsigned p.maximum) (first p) (second p)⟩ (final d) ∧
          (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → final k = regs p k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf (function p) (availIn (function p) result.ctx) 0 3)
            event.ctx fr' (fun key => final (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs p
  let value : Clif.Val := ⟨ty p,Clif.Sem.binary (minmaxOperation p.unsigned p.maximum) (first p) (second p)⟩
  let fr' : Clif.Frame := {frame p with regs := (frame p).regs.set 100 value,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame p) Clif.Mem.empty
      (.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p)) = .ok ([value],Clif.Mem.empty) := by
    rcases p with ⟨u,m,w⟩
    cases u <;> cases m <;> cases w <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame p,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p),[value],
      (frame p).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    all_goals rw [input.results]; rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have restrictedDFG : DFGCons input.event.ctx (restrict (frame p) (availOf (function p) (availIn (function p) input.result.ctx) 0 2)) := dfgCons_congr (ctx := input.event.ctx) (fr := frame p) rfl rfl
    (frame_available p input.result.ctx) input.dfg
  have current : input.record.inst = blockStart (function p) 0 + 2 := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have bits : (ty p).width = if p.wide then 64 else 32 := by rcases p with ⟨u,m,w⟩; cases w <;> rfl
  obtain ⟨u,v,originalX,originalY,d,output,lower,upper,memory,execution⟩ := stock_lower_minmax_wide_source_with_reads
    input.run (scope p) (dominated p) input.events input.records
    (bi := 0) (j := 2) (block := (function p).blocks[0]!) rfl rfl current p.unsigned p.maximum input.source input.clif
    p.wide rfl (by rw [← bits]; exact input.typeX) (by rw [← bits]; exact input.typeY)
    input.results rfl input.mapped input.recorded input.emitted self restrictedDFG
    (input.held.mono (fun _ needed => needed.1)) sourceStep
  have getX : (restrict (frame p) (availOf (function p) (availIn (function p) input.result.ctx) 0 2)).getAs (x p) (ty p) = .ok (first p) :=
    get_constant p input.result.ctx
  have getY : (restrict (frame p) (availOf (function p) (availIn (function p) input.result.ctx) 0 2)).getAs (y p) (ty p) = .ok (second p) :=
    get_parameter p input.result.ctx
  have sameX := Clif.Res.ok.inj (originalX.symm.trans getX)
  have sameY := Clif.Res.ok.inj (originalY.symm.trans getY)
  subst u
  subst v
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,scope p,dominated p,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,lower,upper,sourceStep,execution⟩
end Backend.Stock.Proof.ScalarSelect.WideBothConstantWitness
