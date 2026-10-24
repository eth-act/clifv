import FV.Backend.Proof.StockBnotRecordValues
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.Bnot
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def operand (shifted : Bool) : Nat := if shifted then 63 else 7
private def index (shifted : Bool) : Nat := if shifted then 2 else 0
private def resultKey (shifted : Bool) : Nat := if shifted then 195 else 193
private def function (shifted : Bool) (ty : Clif.Ty) : Clif.Function := {
  name := "stock_bnot_values"
  sig := {params := [⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty)],body :=
    (if shifted then [⟨[31],.iconst ty (BitVec.ofNat ty.width 3)⟩,⟨[63],.binary .ishl ty 7 31⟩] else []) ++
      [⟨[100],.unary .bnot ty (operand shifted)⟩],term := .ret [100]}] }
private def built (shifted : Bool) (ty : Clif.Ty) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function shifted ty)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (shifted : Bool) (ty : Clif.Ty) : Clif.Frame := {
  func := function shifted ty
  regs := fun x => if x = 7 then some (.ofInt ty 7) else
    if shifted ∧ x = 31 then some (.ofInt ty 3) else if shifted ∧ x = 63 then some (.ofInt ty 56) else none
  slots := [],body := [⟨[100],.unary .bnot ty (operand shifted)⟩],term := .ret [100] }
private def regs (n : Nat) : CV := if n = 192 then 7 else 0
private def demand : Array Nat := (Array.replicate 101 0).modify 7 (·+1) |>.modify 100 (·+1)
private theorem scope (shifted : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) : LowerScope (function shifted ty) :=
  lowerScope_of (by rcases supported with rfl | rfl <;> cases shifted <;> decide +kernel)
private theorem dfg (shifted : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) :
    DFGCons (built shifted ty).1 (frame shifted ty) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : (built shifted ty).1.defInst? 7 = none := by rcases supported with rfl | rfl <;> cases shifted <;> rfl
      rw [absent] at defined; cases defined
    · by_cases thirtyone : x = 31
      · subst x
        cases shifted
        · rcases supported with rfl | rfl <;> change none = some j at defined <;> cases defined
        · rcases supported with rfl | rfl
          all_goals
            change some 0 = some j at defined
            cases defined
            obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
            subst info
            cases original
            cases lookup
            exact ⟨[_],fun cm => rfl,rfl⟩
      · by_cases sixtythree : x = 63
        · subst x
          cases shifted
          · rcases supported with rfl | rfl <;> change none = some j at defined <;> cases defined
          · rcases supported with rfl | rfl
            all_goals
              change some 1 = some j at defined
              cases defined
              obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
              subst info
              cases original
              cases lookup
              exact ⟨[_],fun cm => rfl,rfl⟩
        · simp [frame,seven,thirtyone,sixtythree] at lookup
  · intro x t v typed lookup
    by_cases present : x = 7 ∨ x = 31 ∨ x = 63
    · rcases present with rfl | rfl | rfl <;> cases shifted <;> rcases supported with rfl | rfl
      all_goals
        first
        | (change none = some t at typed; cases typed)
        | (change some (.int 32) = some t at typed; cases typed; cases lookup; rfl)
        | (change some (.int 64) = some t at typed; cases typed; cases lookup; rfl)
    · simp only [not_or] at present
      simp [frame,present.1,present.2.1,present.2.2] at lookup

private def sourceKey (info : IInfo) := (info.clif,info.results)
private def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
private theorem dfg_transport {a b : Ctx} {fr : Clif.Frame}
    (insts : a.insts.map sourceKey = b.insts.map sourceKey)
    (types : a.valTy = b.valTy) (defs : a.valDef = b.valDef) (dfg : DFGCons b fr) : DFGCons a fr := by
  constructor
  · intro x j info cl v defined found original pure lookup
    have view : (b.insts[j]?).map sourceKey = some (sourceKey info) := by
      rw [← Array.getElem?_map,← insts,Array.getElem?_map,found]
      rfl
    obtain ⟨info',found',same⟩ := Option.map_eq_some_iff.mp view
    have clifEq := congrArg Prod.fst same
    have resultsEq := congrArg Prod.snd same
    change info'.clif = info.clif at clifEq
    change info'.results = info.results at resultsEq
    obtain ⟨vals,evaluated,written⟩ := dfg.1 x j info' cl v
      (by simpa only [Ctx.defInst?,defs] using defined) found' (clifEq.trans original) pure lookup
    exact ⟨vals,evaluated,by rw [← resultsEq]; exact written⟩
  · simpa only [FrameTyped,Ctx.valueType?,types] using dfg.2

section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed (shifted : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) :
    (Stock.lower (function shifted ty)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && result.blockScans.toList.any (fun event =>
        decide (ctxKey event.ctx = ctxKey (built shifted ty).1) && event.output.records.any (fun record =>
          record.inst == index shifted && decide (record.output.state.demand = demand) &&
          record.output.step.any (fun step => step.decision == .emitted && decide (step.rules.getLast? = some (rule shifted).id))))) = some true := by
  rcases supported with rfl | rfl <;> cases shifted <;> decide +kernel
end Runs

private structure Inputs (shifted : Bool) (ty : Clif.Ty) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function shifted ty) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = index shifted
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.unary .bnot ty (operand shifted))
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg (resultKey shifted) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (rule shifted).id
  dfg : DFGCons event.ctx (frame shifted ty)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame shifted ty)
    (fun k => regs (aliasNum result.final.alias k))

private theorem inputs (shifted : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) :
    Nonempty (Inputs shifted ty) := by
  have actual := observed shifted ty supported
  cases run : Stock.lower (function shifted ty) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,event,events,ctxEq,record,records,current,demand,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some (rule shifted).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.unary .bnot ty (operand shifted)),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      rcases supported with rfl | rfl <;> cases shifted <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.unary .bnot ty (operand shifted)) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg (resultKey shifted) .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl <;> cases shifted <;> rfl
    have actualDFG : DFGCons event.ctx (frame shifted ty) := dfg_transport insts types defs (dfg shifted ty supported)
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame shifted ty)
        (fun n => regs (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt ty 7) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rcases supported with rfl | rfl <;> cases shifted <;> rfl
        · dsimp only
          rw [alias192]
          rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          rw [Demanded,demand] at needed
          change 0 ≠ 0 at needed
          exact False.elim (needed rfl)
        · by_cases sixtythree : x = 63
          · subst x
            rw [Demanded,demand] at needed
            change 0 ≠ 0 at needed
            exact False.elim (needed rfl)
          · simp [frame,seven,thirtyone,sixtythree] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,actualDFG,held⟩⟩

/-- At32/64 bits, actual complete base/fused-shift NOT records establish the
original unary value without materializing the sunk shift/constant in machine
registers; only the fresh destination changes. -/
theorem stock_lower_bnot_record_values_witness (shifted : Bool) (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV),
      Stock.lower (function shifted ty) = .ok result ∧ LowerScope (function shifted ty) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot (BitVec.ofNat ty.width (if shifted then 56 else 7))⟩
        (ρ' record.input.base.nextVreg) ∧ ∀ n, n ≠ record.input.base.nextVreg → ρ' n = regs n := by
  obtain ⟨input⟩ := inputs shifted ty supported
  have get : (frame shifted ty).getAs (operand shifted) ty =
      .ok (BitVec.ofNat ty.width (if shifted then 56 else 7)) := by
    rcases supported with rfl | rfl <;> cases shifted <;> rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_bnot_record_values
    input.run (scope shifted ty supported) input.events input.records shifted input.source input.clif input.results
    input.mapped input.recorded input.emitted input.selectedId self input.dfg input.held get
  exact ⟨input.result,input.event,input.record,ρ',input.run,scope shifted ty supported,input.events,input.records,execution,value,kept⟩

private theorem dominated (shifted : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) : Dominated (function shifted ty) := by
  constructor
  · cases shifted
    · change ([7,100] : List Nat).Nodup; decide +kernel
    · change ([7,31,63,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function] at block
      subst b
      constructor
      · intro j stm statement y member
        cases shifted
        · cases j <;> simp [operand] at statement
          subst stm
          change y ∈ [7] at member
          have equal := List.mem_singleton.mp member
          subst y
          simp [availOf,function,operand,defsBefore,defsFrom]
        · cases j with
          | zero => simp at statement; subst stm; cases member
          | succ j =>
            cases j with
            | zero =>
              simp at statement
              subst stm
              change y ∈ [7,31] at member
              simp only [List.mem_cons,List.not_mem_nil,or_false] at member
              rcases member with rfl | rfl <;> simp [availOf,function,operand,defsBefore,defsFrom]
            | succ j =>
              cases j <;> simp [operand] at statement
              subst stm
              change y ∈ [63] at member
              have equal := List.mem_singleton.mp member
              subst y
              simp [availOf,function,operand,defsBefore,defsFrom]
      · intro y member
        have equal : y = 100 := by
          rcases supported with rfl | rfl <;> change y ∈ [100] at member <;> exact List.mem_singleton.mp member
        subst y
        cases shifted <;> simp [availOf,function,operand,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function shifted ty) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function shifted ty).blocks.length = 1 := rfl
    omega

private theorem frame_available (shifted : Bool) (ty : Clif.Ty) (ctx : Ctx) :
    (restrict (frame shifted ty) (availOf (function shifted ty) (availIn (function shifted ty) ctx) 0 (index shifted))).regs =
      (frame shifted ty).regs := by
  funext x
  by_cases seven : x = 7
  · subst x
    apply restrict_regs_of_mem
    cases shifted <;> simp [availOf,function,operand,index,defsBefore,defsFrom]
  · by_cases thirtyone : x = 31
    · subst x
      cases shifted
      · simp [restrict,frame,seven]
      · apply restrict_regs_of_mem; simp [availOf,function,operand,index,defsBefore,defsFrom]
    · by_cases sixtythree : x = 63
      · subst x
        cases shifted
        · simp [restrict,frame,seven]
        · apply restrict_regs_of_mem; simp [availOf,function,operand,index,defsBefore,defsFrom]
      · simp [restrict,frame,seven,thirtyone,sixtythree]

/-- Actual base/fused-shift NOT source steps inhabit the availability guard and
transfer into the real resulting source frame at32/64 bits. -/
theorem stock_lower_bnot_source_values_witness (shifted : Bool) (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function shifted ty) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs ρ' ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame shifted ty,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (function shifted ty) (availIn (function shifted ty) result.ctx) 0 (index shifted+1))
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := inputs shifted ty supported
  have get : (frame shifted ty).getAs (operand shifted) ty =
      .ok (BitVec.ofNat ty.width (if shifted then 56 else 7)) := by
    rcases supported with rfl | rfl <;> cases shifted <;> rfl
  have restrictedGet := getAs_congr (fr := frame shifted ty) (x := operand shifted) (ty := ty)
    (congrFun (frame_available shifted ty input.result.ctx) (operand shifted))
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := frame shifted ty)
    (fr' := restrict (frame shifted ty) (availOf (function shifted ty) (availIn (function shifted ty) input.result.ctx) 0 (index shifted)))
    rfl rfl (frame_available shifted ty input.result.ctx) input.dfg
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (function shifted ty) (availIn (function shifted ty) input.result.ctx) 0 (index shifted)) => h.1)
  have block : (function shifted ty).blocks[0]? = some ((function shifted ty).blocks[0]!) := rfl
  have statement : ((function shifted ty).blocks[0]!).body[index shifted]? =
      some (⟨[100],.unary .bnot ty (operand shifted)⟩ : Clif.Stmt) := by cases shifted <;> rfl
  have current : input.record.inst = blockStart (function shifted ty) 0 + index shifted := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨ρ',execution,value,kept,installed⟩ := stock_lower_bnot_available_values input.run (scope shifted ty supported)
    (dominated shifted ty supported) input.events input.records block statement current shifted input.source input.clif input.results rfl
    input.mapped input.recorded input.emitted input.selectedId self restrictedDFG guarded (restrictedGet.trans get)
  let val : Clif.Val := ⟨ty,Clif.Sem.unary .bnot (BitVec.ofNat ty.width (if shifted then 56 else 7))⟩
  let fr' : Clif.Frame := {frame shifted ty with regs := (frame shifted ty).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame shifted ty) Clif.Mem.empty
      (.unary .bnot ty (operand shifted)) = .ok ([val],Clif.Mem.empty) := by
    rcases supported with rfl | rfl <;> cases shifted <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame shifted ty,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.unary .bnot ty (operand shifted),[val],(frame shifted ty).regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have sourceHeld := source_single_result_values input.source input.clif input.results sourceStep evaluated installed
  exact ⟨input.result,input.event,input.record,ρ',fr',input.run,input.events,input.records,execution,sourceStep,sourceHeld⟩

end Backend.Stock.Proof.Bnot
