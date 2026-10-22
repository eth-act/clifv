import FV.Backend.Proof.StockMinMaxNarrowConstantDriverRuns
import FV.Backend.Proof.StockMinMaxActualDispatch
import FV.Backend.Proof.LowerValueRelations
namespace Backend.Stock.Proof.ScalarSelect.NarrowConstantWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ScalarSelect Backend.Stock.Proof.ScalarSelect.MinMaxRegisterFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
/-- Fixture parameters cover all four operations, both widths and operand
positions, and ordinary/nonencodable constants. These are witness parameters. -/
structure Case where
  unsigned : Bool
  maximum : Bool
  half : Bool
  left : Bool
  large : Bool
private def ty (p : Case) := narrowMinmaxTy p.half
private def literal (p : Case) : Nat := narrowConstantLiteral p.half p.large
private def x (p : Case) : Nat := if p.left then 7 else 31
private def y (p : Case) : Nat := if p.left then 31 else 7
private def function (p : Case) := narrowConstantFunction p.unsigned p.maximum p.half p.left p.large
private def built (p : Case) := narrowConstantBuilt p.unsigned p.maximum p.half p.left p.large
private def frame (p : Case) (word : BitVec (ty p).width) : Clif.Frame := {
  func := function p
  regs := fun key => if key = 31 then some ⟨ty p,word⟩ else
    if key = 7 then some (.ofInt (ty p) (literal p)) else none
  slots := [],body := [⟨[100],.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p)⟩],term := .ret [100] }
private def regs (p : Case) (word : BitVec (ty p).width) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+word.toNat)
  else if n = narrowConstantTarget p.half p.large then BitVec.ofNat 128 (2^100+literal p)
  else 0
private theorem scope (p : Case) : LowerScope (function p) := by
  apply lowerScope_of
  rcases p with ⟨u,m,w,l,g⟩
  cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> decide +kernel
private theorem absent (p : Case) : (built p).1.defInst? 31 = none := by
  rcases p with ⟨u,m,w,l,g⟩
  cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
private theorem defined (p : Case) : (built p).1.defInst? 7 = some 0 := by
  rcases p with ⟨u,m,w,l,g⟩
  cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
private theorem typed (p : Case) (key : Nat) (present : key = 31 ∨ key = 7) :
    (built p).1.valueType? key = some (.int (ty p).width) := by
  rcases present with rfl | rfl
  all_goals rcases p with ⟨u,m,w,l,g⟩
  all_goals cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
private theorem constant (p : Case) :
    ((built p).1.insts[0]?).map minmaxSourceKey =
      some (some (.iconst (ty p) (BitVec.ofNat (ty p).width (literal p))),[7]) := by
  rcases p with ⟨u,m,w,l,g⟩
  cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
private theorem dfg_base (p : Case) (word : BitVec (ty p).width) : DFGCons (built p).1 (frame p word) := by
  constructor
  · intro key j info cl value defn found original pure lookup
    by_cases parameter : key = 31
    · subst key
      rw [absent p] at defn
      cases defn
    · by_cases fixed : key = 7
      · subst key
        rw [defined p] at defn
        cases defn
        have metadata := constant p
        rw [found] at metadata
        have pair := Option.some.inj metadata
        have clifEq := congrArg Prod.fst pair
        have resultsEq := congrArg Prod.snd pair
        change info.clif = some (.iconst (ty p) (BitVec.ofNat (ty p).width (literal p))) at clifEq
        change info.results = [7] at resultsEq
        have clEq := Option.some.inj (original.symm.trans clifEq)
        subst cl
        change some (.ofInt (ty p) (literal p)) = some value at lookup
        cases lookup
        refine ⟨[.ofInt (ty p) (literal p)],?_,?_⟩
        · intro cm
          rcases p with ⟨u,m,w,l,g⟩
          cases w <;> cases g <;> rfl
        · rw [resultsEq]
          rfl
      · simp [frame,parameter,fixed] at lookup
  · intro key t value typeEq lookup
    by_cases present : key = 31 ∨ key = 7
    · have typeKey := typed p key present
      rw [typeKey] at typeEq
      cases typeEq
      rcases present with rfl | rfl
      all_goals cases lookup
      all_goals rcases p with ⟨u,m,w,l,g⟩
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
private theorem dirty_word (p : Case) (word : BitVec (ty p).width) :
    (BitVec.ofNat 128 (2^100+word.toNat)).setWidth (ty p).width = word := by
  have bound : (ty p).width ≤ 128 := by rcases p with ⟨u,m,w,l,g⟩; cases w <;> simp only [ty,narrowMinmaxTy,Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false] <;> decide
  have high : 2^100 % 2^(ty p).width = 0 := by rcases p with ⟨u,m,w,l,g⟩; cases w <;> simp only [ty,narrowMinmaxTy,Clif.Ty.width,Bool.false_eq_true,ite_true,ite_false] <;> decide +kernel
  rw [BitVec.setWidth_ofNat_of_le bound]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.add_mod,high,Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
private structure Inputs (p : Case) (word : BitVec (ty p).width) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function p) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = 1
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p))
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int)
  typeX : event.ctx.valueType? (x p) = some (.int (ty p).width)
  typeY : event.ctx.valueType? (y p) = some (.int (ty p).width)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (minmaxRule p.unsigned p.maximum).id
  dfg : DFGCons event.ctx (frame p word)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame p word)
    (fun k => regs p word (aliasNum result.final.alias k))
private theorem inputs (p : Case) (word : BitVec (ty p).width) : Nonempty (Inputs p word) := by
  have actual := stock_minmax_narrow_constant_driver_observed p.unsigned p.maximum p.half p.left p.large
  unfold narrowConstantObserved at actual
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
      rcases p with ⟨u,m,w,l,g⟩
      cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p)) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases p with ⟨u,m,w,l,g⟩
      cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
    have typeX : event.ctx.valueType? (x p) = some (.int (ty p).width) := by
      simp only [Ctx.valueType?,types]
      rcases p with ⟨u,m,w,l,g⟩
      cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
    have typeY : event.ctx.valueType? (y p) = some (.int (ty p).width) := by
      simp only [Ctx.valueType?,types]
      rcases p with ⟨u,m,w,l,g⟩
      cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame p word)
        (fun n => regs p word (aliasNum result.final.alias n)) := by
      intro key needed value lookup
      by_cases parameter : key = 31
      · subst key
        change some ⟨ty p,word⟩ = some value at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rcases p with ⟨u,m,w,l,g⟩
          cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
        · change (regs p word (aliasNum result.final.alias 192)).setWidth (ty p).width = word
          rw [alias192]
          change (BitVec.ofNat 128 (2^100+word.toNat)).setWidth (ty p).width = word
          exact dirty_word p word
      · by_cases fixed : key = 7
        · subst key
          change some (.ofInt (ty p) (literal p)) = some value at lookup
          cases lookup
          refine ⟨193,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            rcases p with ⟨u,m,w,l,g⟩
            cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
          · change (regs p word (aliasNum result.final.alias 193)).setWidth (ty p).width = BitVec.ofNat (ty p).width (literal p)
            rw [alias193]
            rcases p with ⟨u,m,w,l,g⟩
            cases w <;> cases g <;> dsimp [regs,ty,literal,narrowConstantTarget,narrowMinmaxTy] <;> decide +kernel
        · simp [frame,parameter,fixed] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,typeX,typeY,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base p word),held⟩⟩
private theorem dominated (p : Case) : Dominated (function p) := by
  constructor
  · change ([31,7,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function,narrowConstantFunction] at block
      subst b
      constructor
      · intro j stm statement key member
        cases j with
        | zero => simp at statement; subst stm; change key ∈ ([] : List Nat) at member; cases member
        | succ j =>
          cases j with
          | zero =>
            simp at statement
            subst stm
            have present : key = 7 ∨ key = 31 := by
              cases h : p.left <;> simpa [Driver.instArgs,x,y,h,or_comm] using member
            rcases present with rfl | rfl <;> simp [availOf,function,narrowConstantFunction,defsBefore,defsFrom]
          | succ j => simp at statement
      · intro key member
        have present : key ∈ [100] := by rcases p with ⟨u,m,w,l,g⟩; cases w <;> exact member
        have equal := List.mem_singleton.mp present
        subst key
        simp [availOf,function,narrowConstantFunction,defsBefore,defsFrom]
    | succ bi => simp [function,narrowConstantFunction] at block
  · intro ctx ranges st build tl key available notLocal other member
    have bound := (inFix_fixOk (f := function p) (ctx := ctx) (gn := id)).cand tl key available
    have length : (function p).blocks.length = 1 := rfl
    omega
private theorem frame_available (p : Case) (word : BitVec (ty p).width) (ctx : Ctx) :
    (restrict (frame p word) (availOf (function p) (availIn (function p) ctx) 0 1)).regs = (frame p word).regs := by
  funext key
  by_cases present : key = 31 ∨ key = 7
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,narrowConstantFunction,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]
private theorem get_parameter (p : Case) (word : BitVec (ty p).width) (ctx : Ctx) :
    (restrict (frame p word) (availOf (function p) (availIn (function p) ctx) 0 1)).getAs 31 (ty p) = .ok word := by
  have same := getAs_congr (fr := frame p word)
    (fr' := restrict (frame p word) (availOf (function p) (availIn (function p) ctx) 0 1))
    (x := 31) (ty := ty p) (congrFun (frame_available p word ctx) 31)
  rcases p with ⟨u,m,w,l,g⟩
  cases w <;> exact same.trans rfl
private theorem get_constant (p : Case) (word : BitVec (ty p).width) (ctx : Ctx) :
    (restrict (frame p word) (availOf (function p) (availIn (function p) ctx) 0 1)).getAs 7 (ty p) =
      .ok (BitVec.ofNat (ty p).width (literal p)) := by
  have same := getAs_congr (fr := frame p word)
    (fr' := restrict (frame p word) (availOf (function p) (availIn (function p) ctx) 0 1))
    (x := 7) (ty := ty p) (congrFun (frame_available p word ctx) 7)
  rcases p with ⟨u,m,w,l,g⟩
  cases w <;> cases g <;> exact same.trans rfl
private def first (p : Case) (word : BitVec (ty p).width) :=
  if p.left then BitVec.ofNat (ty p).width (literal p) else word
private def second (p : Case) (word : BitVec (ty p).width) :=
  if p.left then word else BitVec.ofNat (ty p).width (literal p)
/-- Complete original Stock.lower/retained/source-step witnesses for all32
single-constant forms and every parameter word, with dirty upper bits and the
actual actual scratch/result final aliases. -/
theorem stock_minmax_narrow_constant_complete_source_witness (p : Case) (word : BitVec (ty p).width) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower (function p) = .ok result ∧ LowerScope (function p) ∧ Dominated (function p) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (minmaxRule p.unsigned p.maximum).id ∧
      step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame p word,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs p word) world
        (fun final _ => VHolds ⟨ty p,Clif.Sem.binary (minmaxOperation p.unsigned p.maximum) (first p word) (second p word)⟩ (final d) ∧
          (∀ k,k < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ k → final k = regs p word k) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf (function p) (availIn (function p) result.ctx) 0 2)
            event.ctx fr' (fun key => final (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs p word
  let value : Clif.Val := ⟨ty p,Clif.Sem.binary (minmaxOperation p.unsigned p.maximum) (first p word) (second p word)⟩
  let fr' : Clif.Frame := {frame p word with regs := (frame p word).regs.set 100 value,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame p word) Clif.Mem.empty
      (.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p)) = .ok ([value],Clif.Mem.empty) := by
    rcases p with ⟨u,m,w,l,g⟩
    cases u <;> cases m <;> cases w <;> cases l <;> cases g <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame p word,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.binary (minmaxOperation p.unsigned p.maximum) (ty p) (x p) (y p),[value],
      (frame p word).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    all_goals rw [input.results]; rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have restrictedDFG : DFGCons input.event.ctx (restrict (frame p word) (availOf (function p) (availIn (function p) input.result.ctx) 0 1)) := dfgCons_congr (ctx := input.event.ctx) (fr := frame p word) rfl rfl
    (frame_available p word input.result.ctx) input.dfg
  have current : input.record.inst = blockStart (function p) 0 + 1 := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have bits : (ty p).width = if p.half then 16 else 8 := by rcases p with ⟨u,m,w,l,g⟩; cases w <;> rfl
  obtain ⟨u,v,originalX,originalY,d,output,lower,upper,memory,execution⟩ := stock_lower_minmax_actual_source_with_reads
    input.run (scope p) (dominated p) input.events input.records
    (bi := 0) (j := 1) (block := (function p).blocks[0]!) rfl rfl current p.unsigned p.maximum input.source input.clif
    input.typeX input.typeY
    input.results rfl input.mapped input.recorded input.emitted self restrictedDFG
    (input.held.mono (fun _ needed => needed.1)) sourceStep
  have getX : (restrict (frame p word) (availOf (function p) (availIn (function p) input.result.ctx) 0 1)).getAs (x p) (ty p) = .ok (first p word) := by
    cases h : p.left
    · simpa only [x,first,h,Bool.false_eq_true,ite_false] using get_parameter p word input.result.ctx
    · simpa only [x,first,h,ite_true] using get_constant p word input.result.ctx
  have getY : (restrict (frame p word) (availOf (function p) (availIn (function p) input.result.ctx) 0 1)).getAs (y p) (ty p) = .ok (second p word) := by
    cases h : p.left
    · simpa only [y,second,h,Bool.false_eq_true,ite_false] using get_constant p word input.result.ctx
    · simpa only [y,second,h,ite_true] using get_parameter p word input.result.ctx
  have sameX := Clif.Res.ok.inj (originalX.symm.trans getX)
  have sameY := Clif.Res.ok.inj (originalY.symm.trans getY)
  subst u
  subst v
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,scope p,dominated p,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,lower,upper,sourceStep,execution⟩
end Backend.Stock.Proof.ScalarSelect.NarrowConstantWitness
