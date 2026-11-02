import FV.Backend.Proof.StockRotateSourceValues
import FV.Backend.Proof.LowerValueRelations
namespace Backend.Stock.Proof.ScalarRotate.RightRegisterWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def sourceSlot (aliased : Bool) : Nat := if aliased then 193 else 192
private def countSlot (aliased : Bool) : Nat := if aliased then 192 else 193
private def allocation (w : Nat) : Nat := if w = 8 ∨ w = 16 then 7 else 1
private def rootIndex (aliased : Bool) : Nat := if aliased then 1 else 0
private def instruction (ty : Clif.Ty) : Clif.Inst := .binary .rotr ty 7 13
private def function (ty : Clif.Ty) (aliased : Bool) : Clif.Function := {
  name := "stock_count_source_values"
  sig := {params := (if aliased then [⟨.i64,.none,.normal⟩] else [⟨ty,.none,.normal⟩,⟨.i64,.none,.normal⟩]),returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := (if aliased then [(13,.i64)] else [(7,ty),(13,.i64)]),body :=
    (if aliased then [⟨[7],.iconst ty (BitVec.ofInt ty.width (-91))⟩] else []) ++ [⟨[100],instruction ty⟩],term := .ret [100]}] }
private def built (ty : Clif.Ty) (aliased : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function ty aliased)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (ty : Clif.Ty) (aliased : Bool) : Clif.Frame := {
  func := function ty aliased,regs := fun x => if x = 7 then some (.ofInt ty (-91)) else if x = 13 then some (.ofInt .i64 77) else none,
  slots := [],body := [⟨[100],instruction ty⟩],term := .ret [100] }
private def regs (ty : Clif.Ty) (aliased : Bool) (n : Nat) : CV :=
  if n = (if aliased then 195+allocation ty.width else 192) then BitVec.ofNat 128 (2^100+2^ty.width+(Clif.Val.ofInt ty (-91)).bits.toNat) else if n = countSlot aliased then BitVec.ofNat 128 (2^100+2^64+77) else 0
private def demand : Array Nat := (Array.replicate 101 0).modify 7 (·+1) |>.modify 13 (·+1) |>.modify 100 (·+1)
private def sourceKey (info : IInfo) := (info.clif,info.results)
private def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
private theorem scope (ty : Clif.Ty) (aliased : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : LowerScope (function ty aliased) :=
  lowerScope_of (by cases aliased <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel)

section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private def observedReport (ty : Clif.Ty) (aliased : Bool) : Option Bool :=
  (Stock.lower (function ty aliased)).toOption.map (fun result =>
    decide (aliasNum result.final.alias (sourceSlot aliased) = if aliased then 195+allocation ty.width else sourceSlot aliased) && decide (aliasNum result.final.alias (countSlot aliased) = countSlot aliased) && result.blockScans.toList.any (fun event =>
      decide (ctxKey event.ctx = ctxKey (built ty aliased).1) && event.output.records.any (fun record =>
        record.inst == rootIndex aliased && decide (record.output.state.demand = demand) &&
        record.input.base.nextVreg == 195 && record.output.step.any (fun step => step.decision == .emitted &&
          decide (step.rules.getLast? = some (rotateRule false false ty.width).id)))))
private theorem observed_i8_false : observedReport .i8 false = some true := by decide +kernel
private theorem observed_i8_true : observedReport .i8 true = some true := by decide +kernel
private theorem observed_i16_false : observedReport .i16 false = some true := by decide +kernel
private theorem observed_i16_true : observedReport .i16 true = some true := by decide +kernel
private theorem observed_i32_false : observedReport .i32 false = some true := by decide +kernel
private theorem observed_i32_true : observedReport .i32 true = some true := by decide +kernel
private theorem observed_i64_false : observedReport .i64 false = some true := by decide +kernel
private theorem observed_i64_true : observedReport .i64 true = some true := by decide +kernel
private theorem observed (ty : Clif.Ty) (aliased : Bool) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : observedReport ty aliased = some true := by
  cases aliased <;> rcases supported with rfl | rfl | rfl | rfl
  · exact observed_i8_false
  · exact observed_i16_false
  · exact observed_i32_false
  · exact observed_i64_false
  · exact observed_i8_true
  · exact observed_i16_true
  · exact observed_i32_true
  · exact observed_i64_true
end Runs

private theorem dfg_base (ty : Clif.Ty) (aliased : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    DFGCons (built ty aliased).1 (frame ty aliased) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      cases aliased
      · have absent : (built ty false).1.defInst? 7 = none := by
          rcases supported with rfl | rfl | rfl | rfl <;> rfl
        rw [absent] at defined; cases defined
      · rcases supported with rfl | rfl | rfl | rfl
        all_goals
          change some 0 = some j at defined
          cases defined
          obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
          subst info
          cases original
          cases lookup
          exact ⟨[_],fun cm => rfl,rfl⟩
    · by_cases thirteen : x = 13
      · subst x
        have absent : (built ty aliased).1.defInst? 13 = none := by
          rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
        rw [absent] at defined; cases defined
      · simp [frame,seven,thirteen] at lookup
  · intro x t v typed lookup
    by_cases seven : x = 7
    · subst x
      cases aliased <;> rcases supported with rfl | rfl | rfl | rfl
      all_goals
        change some (.int _) = some t at typed
        cases typed
        cases lookup
        rfl
    · by_cases thirteen : x = 13
      · subst x
        cases aliased <;> rcases supported with rfl | rfl | rfl | rfl
        all_goals
          change some (.int 64) = some t at typed
          cases typed; cases lookup; rfl
      · simp [frame,seven,thirteen] at lookup
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
private structure Inputs (ty : Clif.Ty) (aliased : Bool) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function ty aliased) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = rootIndex aliased
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (instruction ty)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int)
  sourceMapped : event.ctx.valueReg? 7 = some (.vreg (sourceSlot aliased) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (rotateRule false false ty.width).id
  dfg : DFGCons event.ctx (frame ty aliased)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty aliased)
    (fun k => regs ty aliased (aliasNum result.final.alias k))
private theorem inputs (ty : Clif.Ty) (aliased : Bool) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : Nonempty (Inputs ty aliased) := by
  have actual := observed ty aliased supported
  unfold observedReport at actual
  cases run : Stock.lower (function ty aliased) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,demandEq,frontier,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some (rotateRule false false ty.width).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey = some (some (instruction ty),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (instruction ty) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
    have sourceMapped : event.ctx.valueReg? 7 = some (.vreg (sourceSlot aliased) .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty aliased)
        (fun k => regs ty aliased (aliasNum result.final.alias k)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt ty (-91)) = some val at lookup
        cases lookup
        refine ⟨sourceSlot aliased,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
        · dsimp only; rw [alias192]
          rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> unfold VHolds <;> decide +kernel
      · by_cases thirteen : x = 13
        · subst x
          change some (.ofInt .i64 77) = some val at lookup
          cases lookup
          refine ⟨countSlot aliased,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
          · have alias193 : aliasNum result.final.alias (countSlot aliased) = countSlot aliased := by assumption
            dsimp only; rw [alias193]
            rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> unfold VHolds <;> decide +kernel
        · simp [frame,seven,thirteen] at lookup
    have dfg := dfg_transport insts types defs (dfg_base ty aliased supported)
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,sourceMapped,
      recorded,emitted,selectedId,dfg,held⟩⟩
private theorem dominated (ty : Clif.Ty) (aliased : Bool) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : Dominated (function ty aliased) := by
  constructor
  · cases aliased
    · change ([7,13,100] : List Nat).Nodup; decide +kernel
    · change ([13,7,100] : List Nat).Nodup; decide +kernel
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
          change v ∈ [7,13] at member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
        · cases j
          · simp at statement; subst stm; cases member
          · rename_i j
            cases j <;> simp at statement
            subst stm
            change v ∈ [7,13] at member
            simp only [List.mem_cons,List.not_mem_nil,or_false] at member
            rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
      · intro v member
        have narrowed : v ∈ [100] := by rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> exact member
        have equal := List.mem_singleton.mp narrowed
        subst v
        cases aliased <;> simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function ty aliased) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function ty aliased).blocks.length = 1 := rfl
    omega
private theorem frame_available (ty : Clif.Ty) (aliased : Bool) (ctx : Ctx) :
    (restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) ctx) 0
      (rootIndex aliased))).regs = (frame ty aliased).regs := by
  funext x
  by_cases seven : x = 7
  · subst x
    apply restrict_regs_of_mem
    cases aliased <;> simp [availOf,function,rootIndex,defsBefore,defsFrom]
  · by_cases thirteen : x = 13
    · subst x; apply restrict_regs_of_mem
      cases aliased <;> simp [availOf,function,rootIndex,defsBefore,defsFrom]
    · simp [restrict,frame,seven,thirteen]
/-- All four scalar widths have actual complete source/record witnesses,
including earlier-producer reads through final aliases with unmaterialized
original source registers and dirty upper machine bits. -/
theorem stock_lower_rotate_source_witness (ty : Clif.Ty) (aliased : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function ty aliased) = .ok result ∧ LowerScope (function ty aliased) ∧ Dominated (function ty aliased) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (rotateRule false false ty.width).id ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs ty aliased) ρ' ∧
      VHolds ⟨ty,rotateWideBits false (BitVec.ofInt ty.width (-91)) 77⟩ (ρ' d) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame ty aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf (function ty aliased) (availIn (function ty aliased) result.ctx) 0 (rootIndex aliased+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (aliased = true → regs ty aliased (sourceSlot aliased) = 0) := by
  obtain ⟨input⟩ := inputs ty aliased supported
  have sameFrame := frame_available ty aliased input.result.ctx
  have getX : (restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0
      (rootIndex aliased))).getAs 7 ty = .ok (BitVec.ofInt ty.width (-91)) := by
    have original : (frame ty aliased).getAs 7 ty = .ok (BitVec.ofInt ty.width (-91)) := by
      rcases supported with rfl | rfl | rfl | rfl <;> rfl
    exact (getAs_congr (fr := frame ty aliased) (x := 7) (ty := ty) (congrFun sameFrame 7)).trans original
  have guarded := input.held.mono (fun v (h : Demanded input.record.output.state v ∧
      v ∈ availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0 (rootIndex aliased)) => h.1)
  let val : Clif.Val := ⟨ty,rotateWideBits false (BitVec.ofInt ty.width (-91)) 77⟩
  let fr' : Clif.Frame := {frame ty aliased with regs := (frame ty aliased).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame ty aliased) Clif.Mem.empty (instruction ty) =
      .ok ([val],Clif.Mem.empty) := by rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame ty aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,instruction ty,[val],(frame ty aliased).regs.set 100 val,[],input.source,input.clif,
      by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have block : (function ty aliased).blocks[0]? = some ((function ty aliased).blocks[0]!) := rfl
  have statement : ((function ty aliased).blocks[0]!).body[rootIndex aliased]? = some (⟨[100],instruction ty⟩ : Clif.Stmt) := by
    cases aliased <;> rfl
  have current : input.record.inst = blockStart (function ty aliased) 0 + rootIndex aliased := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := frame ty aliased)
    (fr' := restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0 (rootIndex aliased))) rfl rfl sameFrame input.dfg
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨actual,actualAmount,d,ρ',found,foundAmount,output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_rotate_source_by_instruction input.run
    (scope ty aliased supported) (dominated ty aliased supported) false input.events input.records block statement current
    input.source input.clif input.results rfl input.mapped input.recorded input.emitted self restrictedDFG guarded sourceStep
  have actualEq := Clif.Res.ok.inj (found.symm.trans getX)
  subst actual
  have originalY : (frame ty aliased).regs 13 = some (.ofInt .i64 77) := rfl
  have getY := (congrFun sameFrame 13).trans originalY
  have amountEq := Option.some.inj (foundAmount.symm.trans getY)
  subst actualAmount
  exact ⟨input.result,input.event,input.record,input.step,d,ρ',fr',input.run,scope ty aliased supported,dominated ty aliased supported,
    input.events,input.records,input.recorded,input.emitted,input.selectedId,output,bounds,execution,value,sourceStep,post,fun yes => by
      subst aliased
      have separate : (193 : Nat) ≠ 195+allocation ty.width := by unfold allocation; split <;> (try simp only [ite_true,ite_false,Bool.false_eq_true]) <;> omega
      simp [regs,sourceSlot,countSlot,separate]⟩

end Backend.Stock.Proof.ScalarRotate.RightRegisterWitness
namespace Backend.Stock.Proof.ScalarRotate.RightRegisterWitness.ZeroCount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frame (ty : Clif.Ty) (aliased : Bool) : Clif.Frame := {
  func := function ty aliased,regs := fun x => if x = 7 then some (.ofInt ty (-91)) else if x = 13 then some (.ofInt .i64 0) else none,
  slots := [],body := [⟨[100],instruction ty⟩],term := .ret [100] }
private def regs (ty : Clif.Ty) (aliased : Bool) (n : Nat) : CV :=
  if n = (if aliased then 195+allocation ty.width else 192) then BitVec.ofNat 128 (2^100+2^ty.width+(Clif.Val.ofInt ty (-91)).bits.toNat) else if n = countSlot aliased then BitVec.ofNat 128 (2^100+2^64+0) else 0
private theorem dfg_base (ty : Clif.Ty) (aliased : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    DFGCons (built ty aliased).1 (frame ty aliased) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      cases aliased
      · have absent : (built ty false).1.defInst? 7 = none := by
          rcases supported with rfl | rfl | rfl | rfl <;> rfl
        rw [absent] at defined; cases defined
      · rcases supported with rfl | rfl | rfl | rfl
        all_goals
          change some 0 = some j at defined
          cases defined
          obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
          subst info
          cases original
          cases lookup
          exact ⟨[_],fun cm => rfl,rfl⟩
    · by_cases thirteen : x = 13
      · subst x
        have absent : (built ty aliased).1.defInst? 13 = none := by
          rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
        rw [absent] at defined; cases defined
      · simp [frame,seven,thirteen] at lookup
  · intro x t v typed lookup
    by_cases seven : x = 7
    · subst x
      cases aliased <;> rcases supported with rfl | rfl | rfl | rfl
      all_goals
        change some (.int _) = some t at typed
        cases typed
        cases lookup
        rfl
    · by_cases thirteen : x = 13
      · subst x
        cases aliased <;> rcases supported with rfl | rfl | rfl | rfl
        all_goals
          change some (.int 64) = some t at typed
          cases typed; cases lookup; rfl
      · simp [frame,seven,thirteen] at lookup
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
private structure Inputs (ty : Clif.Ty) (aliased : Bool) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function ty aliased) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = rootIndex aliased
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (instruction ty)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int)
  sourceMapped : event.ctx.valueReg? 7 = some (.vreg (sourceSlot aliased) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (rotateRule false false ty.width).id
  dfg : DFGCons event.ctx (frame ty aliased)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty aliased)
    (fun k => regs ty aliased (aliasNum result.final.alias k))
private theorem inputs (ty : Clif.Ty) (aliased : Bool) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : Nonempty (Inputs ty aliased) := by
  have actual := observed ty aliased supported
  unfold observedReport at actual
  cases run : Stock.lower (function ty aliased) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,demandEq,frontier,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some (rotateRule false false ty.width).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey = some (some (instruction ty),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (instruction ty) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
    have sourceMapped : event.ctx.valueReg? 7 = some (.vreg (sourceSlot aliased) .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty aliased)
        (fun k => regs ty aliased (aliasNum result.final.alias k)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt ty (-91)) = some val at lookup
        cases lookup
        refine ⟨sourceSlot aliased,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
        · dsimp only; rw [alias192]
          rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> unfold VHolds <;> decide +kernel
      · by_cases thirteen : x = 13
        · subst x
          change some (.ofInt .i64 0) = some val at lookup
          cases lookup
          refine ⟨countSlot aliased,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
          · have alias193 : aliasNum result.final.alias (countSlot aliased) = countSlot aliased := by assumption
            dsimp only; rw [alias193]
            rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> unfold VHolds <;> decide +kernel
        · simp [frame,seven,thirteen] at lookup
    have dfg := dfg_transport insts types defs (dfg_base ty aliased supported)
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,sourceMapped,
      recorded,emitted,selectedId,dfg,held⟩⟩
private theorem frame_available (ty : Clif.Ty) (aliased : Bool) (ctx : Ctx) :
    (restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) ctx) 0
      (rootIndex aliased))).regs = (frame ty aliased).regs := by
  funext x
  by_cases seven : x = 7
  · subst x
    apply restrict_regs_of_mem
    cases aliased <;> simp [availOf,function,rootIndex,defsBefore,defsFrom]
  · by_cases thirteen : x = 13
    · subst x; apply restrict_regs_of_mem
      cases aliased <;> simp [availOf,function,rootIndex,defsBefore,defsFrom]
    · simp [restrict,frame,seven,thirteen]
/-- All four scalar widths have actual complete source/record witnesses,
including earlier-producer reads through final aliases with unmaterialized
original source registers and dirty upper machine bits. -/
theorem stock_lower_rotate_source_witness (ty : Clif.Ty) (aliased : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function ty aliased) = .ok result ∧ LowerScope (function ty aliased) ∧ Dominated (function ty aliased) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (rotateRule false false ty.width).id ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs ty aliased) ρ' ∧
      VHolds ⟨ty,rotateWideBits false (BitVec.ofInt ty.width (-91)) 0⟩ (ρ' d) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame ty aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf (function ty aliased) (availIn (function ty aliased) result.ctx) 0 (rootIndex aliased+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (aliased = true → regs ty aliased (sourceSlot aliased) = 0) := by
  obtain ⟨input⟩ := inputs ty aliased supported
  have sameFrame := frame_available ty aliased input.result.ctx
  have getX : (restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0
      (rootIndex aliased))).getAs 7 ty = .ok (BitVec.ofInt ty.width (-91)) := by
    have original : (frame ty aliased).getAs 7 ty = .ok (BitVec.ofInt ty.width (-91)) := by
      rcases supported with rfl | rfl | rfl | rfl <;> rfl
    exact (getAs_congr (fr := frame ty aliased) (x := 7) (ty := ty) (congrFun sameFrame 7)).trans original
  have guarded := input.held.mono (fun v (h : Demanded input.record.output.state v ∧
      v ∈ availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0 (rootIndex aliased)) => h.1)
  let val : Clif.Val := ⟨ty,rotateWideBits false (BitVec.ofInt ty.width (-91)) 0⟩
  let fr' : Clif.Frame := {frame ty aliased with regs := (frame ty aliased).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame ty aliased) Clif.Mem.empty (instruction ty) =
      .ok ([val],Clif.Mem.empty) := by rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame ty aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,instruction ty,[val],(frame ty aliased).regs.set 100 val,[],input.source,input.clif,
      by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have block : (function ty aliased).blocks[0]? = some ((function ty aliased).blocks[0]!) := rfl
  have statement : ((function ty aliased).blocks[0]!).body[rootIndex aliased]? = some (⟨[100],instruction ty⟩ : Clif.Stmt) := by
    cases aliased <;> rfl
  have current : input.record.inst = blockStart (function ty aliased) 0 + rootIndex aliased := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := frame ty aliased)
    (fr' := restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0 (rootIndex aliased))) rfl rfl sameFrame input.dfg
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨actual,actualAmount,d,ρ',found,foundAmount,output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_rotate_source_by_instruction input.run
    (scope ty aliased supported) (dominated ty aliased supported) false input.events input.records block statement current
    input.source input.clif input.results rfl input.mapped input.recorded input.emitted self restrictedDFG guarded sourceStep
  have actualEq := Clif.Res.ok.inj (found.symm.trans getX)
  subst actual
  have originalY : (frame ty aliased).regs 13 = some (.ofInt .i64 0) := rfl
  have getY := (congrFun sameFrame 13).trans originalY
  have amountEq := Option.some.inj (foundAmount.symm.trans getY)
  subst actualAmount
  exact ⟨input.result,input.event,input.record,input.step,d,ρ',fr',input.run,scope ty aliased supported,dominated ty aliased supported,
    input.events,input.records,input.recorded,input.emitted,input.selectedId,output,bounds,execution,value,sourceStep,post,fun yes => by
      subst aliased
      have separate : (193 : Nat) ≠ 195+allocation ty.width := by unfold allocation; split <;> (try simp only [ite_true,ite_false,Bool.false_eq_true]) <;> omega
      simp [regs,sourceSlot,countSlot,separate]⟩


end Backend.Stock.Proof.ScalarRotate.RightRegisterWitness.ZeroCount

namespace Backend.Stock.Proof.ScalarRotate.RightRegisterWitness.WrappedCount
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def frame (ty : Clif.Ty) (aliased : Bool) : Clif.Frame := {
  func := function ty aliased,regs := fun x => if x = 7 then some (.ofInt ty (-91)) else if x = 13 then some (.ofInt .i64 64) else none,
  slots := [],body := [⟨[100],instruction ty⟩],term := .ret [100] }
private def regs (ty : Clif.Ty) (aliased : Bool) (n : Nat) : CV :=
  if n = (if aliased then 195+allocation ty.width else 192) then BitVec.ofNat 128 (2^100+2^ty.width+(Clif.Val.ofInt ty (-91)).bits.toNat) else if n = countSlot aliased then BitVec.ofNat 128 (2^100+2^64+64) else 0
private theorem dfg_base (ty : Clif.Ty) (aliased : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    DFGCons (built ty aliased).1 (frame ty aliased) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      cases aliased
      · have absent : (built ty false).1.defInst? 7 = none := by
          rcases supported with rfl | rfl | rfl | rfl <;> rfl
        rw [absent] at defined; cases defined
      · rcases supported with rfl | rfl | rfl | rfl
        all_goals
          change some 0 = some j at defined
          cases defined
          obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
          subst info
          cases original
          cases lookup
          exact ⟨[_],fun cm => rfl,rfl⟩
    · by_cases thirteen : x = 13
      · subst x
        have absent : (built ty aliased).1.defInst? 13 = none := by
          rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
        rw [absent] at defined; cases defined
      · simp [frame,seven,thirteen] at lookup
  · intro x t v typed lookup
    by_cases seven : x = 7
    · subst x
      cases aliased <;> rcases supported with rfl | rfl | rfl | rfl
      all_goals
        change some (.int _) = some t at typed
        cases typed
        cases lookup
        rfl
    · by_cases thirteen : x = 13
      · subst x
        cases aliased <;> rcases supported with rfl | rfl | rfl | rfl
        all_goals
          change some (.int 64) = some t at typed
          cases typed; cases lookup; rfl
      · simp [frame,seven,thirteen] at lookup
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
private structure Inputs (ty : Clif.Ty) (aliased : Bool) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function ty aliased) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = rootIndex aliased
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (instruction ty)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int)
  sourceMapped : event.ctx.valueReg? 7 = some (.vreg (sourceSlot aliased) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (rotateRule false false ty.width).id
  dfg : DFGCons event.ctx (frame ty aliased)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty aliased)
    (fun k => regs ty aliased (aliasNum result.final.alias k))
private theorem inputs (ty : Clif.Ty) (aliased : Bool) (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : Nonempty (Inputs ty aliased) := by
  have actual := observed ty aliased supported
  unfold observedReport at actual
  cases run : Stock.lower (function ty aliased) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,demandEq,frontier,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some (rotateRule false false ty.width).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey = some (some (instruction ty),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (instruction ty) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
    have sourceMapped : event.ctx.valueReg? 7 = some (.vreg (sourceSlot aliased) .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty aliased)
        (fun k => regs ty aliased (aliasNum result.final.alias k)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt ty (-91)) = some val at lookup
        cases lookup
        refine ⟨sourceSlot aliased,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
        · dsimp only; rw [alias192]
          rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> unfold VHolds <;> decide +kernel
      · by_cases thirteen : x = 13
        · subst x
          change some (.ofInt .i64 64) = some val at lookup
          cases lookup
          refine ⟨countSlot aliased,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> rfl
          · have alias193 : aliasNum result.final.alias (countSlot aliased) = countSlot aliased := by assumption
            dsimp only; rw [alias193]
            rcases supported with rfl | rfl | rfl | rfl <;> cases aliased <;> unfold VHolds <;> decide +kernel
        · simp [frame,seven,thirteen] at lookup
    have dfg := dfg_transport insts types defs (dfg_base ty aliased supported)
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,sourceMapped,
      recorded,emitted,selectedId,dfg,held⟩⟩
private theorem frame_available (ty : Clif.Ty) (aliased : Bool) (ctx : Ctx) :
    (restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) ctx) 0
      (rootIndex aliased))).regs = (frame ty aliased).regs := by
  funext x
  by_cases seven : x = 7
  · subst x
    apply restrict_regs_of_mem
    cases aliased <;> simp [availOf,function,rootIndex,defsBefore,defsFrom]
  · by_cases thirteen : x = 13
    · subst x; apply restrict_regs_of_mem
      cases aliased <;> simp [availOf,function,rootIndex,defsBefore,defsFrom]
    · simp [restrict,frame,seven,thirteen]
/-- All four scalar widths have actual complete source/record witnesses,
including earlier-producer reads through final aliases with unmaterialized
original source registers and dirty upper machine bits. -/
theorem stock_lower_rotate_source_witness (ty : Clif.Ty) (aliased : Bool)
    (supported : ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function ty aliased) = .ok result ∧ LowerScope (function ty aliased) ∧ Dominated (function ty aliased) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (rotateRule false false ty.width).id ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs ty aliased) ρ' ∧
      VHolds ⟨ty,rotateWideBits false (BitVec.ofInt ty.width (-91)) 64⟩ (ρ' d) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame ty aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf (function ty aliased) (availIn (function ty aliased) result.ctx) 0 (rootIndex aliased+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (aliased = true → regs ty aliased (sourceSlot aliased) = 0) := by
  obtain ⟨input⟩ := inputs ty aliased supported
  have sameFrame := frame_available ty aliased input.result.ctx
  have getX : (restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0
      (rootIndex aliased))).getAs 7 ty = .ok (BitVec.ofInt ty.width (-91)) := by
    have original : (frame ty aliased).getAs 7 ty = .ok (BitVec.ofInt ty.width (-91)) := by
      rcases supported with rfl | rfl | rfl | rfl <;> rfl
    exact (getAs_congr (fr := frame ty aliased) (x := 7) (ty := ty) (congrFun sameFrame 7)).trans original
  have guarded := input.held.mono (fun v (h : Demanded input.record.output.state v ∧
      v ∈ availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0 (rootIndex aliased)) => h.1)
  let val : Clif.Val := ⟨ty,rotateWideBits false (BitVec.ofInt ty.width (-91)) 64⟩
  let fr' : Clif.Frame := {frame ty aliased with regs := (frame ty aliased).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame ty aliased) Clif.Mem.empty (instruction ty) =
      .ok ([val],Clif.Mem.empty) := by rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame ty aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,instruction ty,[val],(frame ty aliased).regs.set 100 val,[],input.source,input.clif,
      by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have block : (function ty aliased).blocks[0]? = some ((function ty aliased).blocks[0]!) := rfl
  have statement : ((function ty aliased).blocks[0]!).body[rootIndex aliased]? = some (⟨[100],instruction ty⟩ : Clif.Stmt) := by
    cases aliased <;> rfl
  have current : input.record.inst = blockStart (function ty aliased) 0 + rootIndex aliased := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := frame ty aliased)
    (fr' := restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0 (rootIndex aliased))) rfl rfl sameFrame input.dfg
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨actual,actualAmount,d,ρ',found,foundAmount,output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_rotate_source_by_instruction input.run
    (scope ty aliased supported) (dominated ty aliased supported) false input.events input.records block statement current
    input.source input.clif input.results rfl input.mapped input.recorded input.emitted self restrictedDFG guarded sourceStep
  have actualEq := Clif.Res.ok.inj (found.symm.trans getX)
  subst actual
  have originalY : (frame ty aliased).regs 13 = some (.ofInt .i64 64) := rfl
  have getY := (congrFun sameFrame 13).trans originalY
  have amountEq := Option.some.inj (foundAmount.symm.trans getY)
  subst actualAmount
  exact ⟨input.result,input.event,input.record,input.step,d,ρ',fr',input.run,scope ty aliased supported,dominated ty aliased supported,
    input.events,input.records,input.recorded,input.emitted,input.selectedId,output,bounds,execution,value,sourceStep,post,fun yes => by
      subst aliased
      have separate : (193 : Nat) ≠ 195+allocation ty.width := by unfold allocation; split <;> (try simp only [ite_true,ite_false,Bool.false_eq_true]) <;> omega
      simp [regs,sourceSlot,countSlot,separate]⟩


end Backend.Stock.Proof.ScalarRotate.RightRegisterWitness.WrappedCount
