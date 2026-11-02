import FV.Backend.Proof.StockHighMulWitnessRuns
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.ScalarHighMul.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open RunData
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frame (signed : Bool) (ty : Clif.Ty) : Clif.Frame := {
  func := function signed ty
  regs := fun x => if x = 7 then some (.ofInt ty (-7)) else
    if x = 31 then some (.ofInt ty 5) else none
  slots := [],body := [⟨[100],.binary (if signed then .smulhi else .umulhi) ty 7 31⟩],term := .ret [100] }
private def regs (ty : Clif.Ty) (n : Nat) : CV :=
  if n = 192 then BitVec.ofNat 128 (2^100+(BitVec.ofInt ty.width (-7)).toNat)
  else if n = 193 then BitVec.ofNat 128 (2^100+2^ty.width+5) else 0
private theorem scope (signed : Bool) (ty : Clif.Ty) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : LowerScope (function signed ty) :=
  lowerScope_of (by cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel)


private theorem dfg_base (signed : Bool) (ty : Clif.Ty)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : DFGCons (built signed ty).1 (frame signed ty) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : (built signed ty).1.defInst? 7 = none := by cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
      rw [absent] at defined; cases defined
    · by_cases thirtyone : x = 31
      · subst x
        have absent : (built signed ty).1.defInst? 31 = none := by cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
        rw [absent] at defined; cases defined
      · simp [frame,seven,thirtyone] at lookup
  · intro x t v typed lookup
    by_cases present : x = 7 ∨ x = 31
    · rcases present with rfl | rfl <;> cases signed <;> rcases supported with rfl | rfl | rfl | rfl
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
private structure Inputs (signed : Bool) (ty : Clif.Ty) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function signed ty) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = (0 : Nat)
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.binary (if signed then .smulhi else .umulhi) ty 7 31)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (highmulRule signed ty.width).id
  dfg : DFGCons event.ctx (frame signed ty)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame signed ty)
    (fun k => regs ty (aliasNum result.final.alias k))

private theorem inputs (signed : Bool) (ty : Clif.Ty) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    Nonempty (Inputs signed ty) := by
  have actual := observed signed ty supported
  cases run : Stock.lower (function signed ty) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,demand,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some (highmulRule signed ty.width).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.binary (if signed then .smulhi else .umulhi) ty 7 31),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.binary (if signed then .smulhi else .umulhi) ty 7 31) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int) := by
      simp only [Ctx.valueReg?,maps]
      cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame signed ty)
        (fun n => regs ty (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt ty (-7)) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
        · dsimp only
          rw [alias192]
          cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          change some (.ofInt ty 5) = some val at lookup
          cases lookup
          refine ⟨193,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
          · dsimp only
            rw [alias193]
            cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> unfold VHolds <;> decide +kernel
        · simp [frame,seven,thirtyone] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base signed ty supported),held⟩⟩

private theorem dominated (signed : Bool) (ty : Clif.Ty) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : Dominated (function signed ty) := by
  constructor
  · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function] at block
      subst b
      constructor
      · intro j stm statement y member
        cases j <;> simp at statement
        subst stm
        change y ∈ [7,31] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
      · intro y member
        have narrowed : y ∈ [100] := by cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> exact member
        have equal := List.mem_singleton.mp narrowed
        clear member narrowed
        subst y
        simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function signed ty) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function signed ty).blocks.length = 1 := rfl
    omega

private theorem frame_available (signed : Bool) (ty : Clif.Ty) (ctx : Ctx) :
    (restrict (frame signed ty) (availOf (function signed ty) (availIn (function signed ty) ctx) 0 0)).regs = (frame signed ty).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]

/-- Complete signed/unsigned high-multiply records and original source steps
are inhabited at8/16/32/64 bits, including dirty upper machine-register bits. -/
theorem stock_lower_highmul_source_values_witness (signed : Bool) (ty : Clif.Ty)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (u v : BitVec ty.width) (d : Nat) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function signed ty) = .ok result ∧ LowerScope (function signed ty) ∧ Dominated (function signed ty) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (highmulRule signed ty.width).id ∧ step.results = [[.vreg d .int]] ∧
      (restrict (frame signed ty) (availOf (function signed ty) (availIn (function signed ty) result.ctx) 0 0)).getAs 7 ty = .ok u ∧
      (restrict (frame signed ty) (availOf (function signed ty) (availIn (function signed ty) result.ctx) 0 0)).getAs 31 ty = .ok v ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs ty) ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) u v⟩ (ρ' d) ∧
      (∀ n,n < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ n → ρ' n = regs ty n) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame signed ty,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (function signed ty) (availIn (function signed ty) result.ctx) 0 ((0 : Nat)+1))
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := inputs signed ty supported
  have getX : (frame signed ty).getAs 7 ty = .ok (BitVec.ofInt ty.width (-7)) := by
    cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have getY : (frame signed ty).getAs 31 ty = .ok (BitVec.ofNat ty.width 5) := by
    cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have restrictedX := getAs_congr (fr := frame signed ty) (x := 7) (ty := ty)
    (congrFun (frame_available signed ty input.result.ctx) 7)
  have restrictedY := getAs_congr (fr := frame signed ty) (x := 31) (ty := ty)
    (congrFun (frame_available signed ty input.result.ctx) 31)
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (function signed ty) (availIn (function signed ty) input.result.ctx) 0 ((0 : Nat))) => h.1)
  have block : (function signed ty).blocks[0]? = some ((function signed ty).blocks[0]!) := rfl
  have statement : ((function signed ty).blocks[0]!).body[(0 : Nat)]? =
      some (⟨[100],.binary (if signed then .smulhi else .umulhi) ty 7 31⟩ : Clif.Stmt) := by rfl
  have current : input.record.inst = blockStart (function signed ty) 0 + (0 : Nat) := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have restrictedDFG : DFGCons input.event.ctx
      (restrict (frame signed ty) (availOf (function signed ty) (availIn (function signed ty) input.result.ctx) 0 0)) := by
    exact dfgCons_congr (ctx := input.event.ctx) (fr := frame signed ty) rfl rfl
      (frame_available signed ty input.result.ctx) input.dfg
  let val : Clif.Val := ⟨ty,Clif.Sem.binary (if signed then .smulhi else .umulhi) (BitVec.ofInt ty.width (-7)) (BitVec.ofNat ty.width 5)⟩
  let fr' : Clif.Frame := {frame signed ty with regs := (frame signed ty).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame signed ty) Clif.Mem.empty
      (.binary (if signed then .smulhi else .umulhi) ty 7 31) = .ok ([val],Clif.Mem.empty) := by
    cases signed <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame signed ty,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.binary (if signed then .smulhi else .umulhi) ty 7 31,[val],(frame signed ty).regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  obtain ⟨u,v,d,ρ',getX',getY',output,bounds,execution,value,memEq,kept,sourceHeld⟩ :=
    stock_lower_highmul_source_by_instruction input.run (scope signed ty supported) (dominated signed ty supported)
      input.events input.records block statement current signed input.source input.clif input.results rfl
      input.mapped input.recorded input.emitted self restrictedDFG guarded sourceStep
  exact ⟨input.result,input.event,input.record,input.step,u,v,d,ρ',fr',input.run,scope signed ty supported,dominated signed ty supported,
    input.events,input.records,input.recorded,input.emitted,input.selectedId,output,getX',getY',bounds,execution,value,kept,sourceStep,sourceHeld⟩

end Backend.Stock.Proof.ScalarHighMul.Witness
