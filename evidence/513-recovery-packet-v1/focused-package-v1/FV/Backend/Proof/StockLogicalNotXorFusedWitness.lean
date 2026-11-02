import FV.Backend.Proof.StockLogicalNotRecord
import FV.Backend.Proof.StockLogicalNotXorRecord
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.LogicalNot.XorFusedWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def operand (shifted : Bool) : Nat := if shifted then 63 else 64
private def index (shifted : Bool) : Nat := if shifted then 3 else 2
private def resultKey (shifted : Bool) : Nat := if shifted then 197 else 196
private def childIndex (shifted : Bool) : Nat := if shifted then 2 else 1
private def constant (shifted : Bool) : Nat := if shifted then 3 else 255
private def sourceValue (shifted : Bool) : Nat := if shifted then 47 else 248
private def function (shifted : Bool) (ty : Clif.Ty) : Clif.Function := {
  name := "stock_not_xor_fused_values"
  sig := {params := [⟨ty,.none,.normal⟩,⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty),(31,ty)],body :=
    [⟨[64],.iconst ty (BitVec.ofNat ty.width (constant shifted))⟩] ++
    (if shifted then [⟨[63],.binary .ishl ty 31 64⟩] else []) ++
    [⟨[90],.binary .bxor ty 7 (operand shifted)⟩,⟨[100],.unary .bnot ty 90⟩],term := .ret [100]}] }
private def built (shifted : Bool) (ty : Clif.Ty) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function shifted ty)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (shifted : Bool) (ty : Clif.Ty) : Clif.Frame := {
  func := function shifted ty
  regs := fun x => if x = 7 then some (.ofInt ty 7) else
    if x = 31 then some (.ofInt ty 5) else if x = 64 then some (.ofInt ty (constant shifted)) else
    if shifted ∧ x = 63 then some (.ofInt ty 40) else if x = 90 then some (.ofInt ty (sourceValue shifted)) else none
  slots := [],body := [⟨[100],.unary .bnot ty 90⟩],term := .ret [100] }
private def regs (n : Nat) : CV := if n = 192 then 7 else if n = 193 then 5 else 0
private def demand (shifted : Bool) : Array Nat := (Array.replicate 101 0).modify 7 (·+1)
  |>.modify 31 (fun n => if shifted then n+1 else n) |>.modify 100 (·+1)
private theorem scope (shifted : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) : LowerScope (function shifted ty) :=
  lowerScope_of (by cases shifted <;> rcases supported with rfl | rfl <;> decide +kernel)
private theorem dfg (shifted : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) :
    DFGCons (built shifted ty).1 (frame shifted ty) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases param : x = 7 ∨ x = 31
    · rcases param with rfl | rfl
      · have absent : (built shifted ty).1.defInst? 7 = none := by cases shifted <;> rcases supported with rfl | rfl <;> rfl
        rw [absent] at defined; cases defined
      · have absent : (built shifted ty).1.defInst? 31 = none := by cases shifted <;> rcases supported with rfl | rfl <;> rfl
        rw [absent] at defined; cases defined
    · by_cases con : x = 64
      · subst x
        cases shifted <;> rcases supported with rfl | rfl
        all_goals
          change some 0 = some j at defined
          cases defined
          obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
          subst info
          cases original
          cases lookup
          exact ⟨[_],fun cm => rfl,rfl⟩
      · by_cases sh : x = 63
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
        · by_cases child : x = 90
          · subst x
            cases shifted <;> rcases supported with rfl | rfl
            all_goals
              change some _ = some j at defined
              cases defined
              obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
              subst info
              cases original
              cases lookup
              exact ⟨[_],fun cm => rfl,rfl⟩
          · simp only [not_or] at param
            simp [frame,param.1,param.2,con,sh,child] at lookup
  · intro x t v typed lookup
    by_cases present : x = 7 ∨ x = 31 ∨ x = 64 ∨ x = 63 ∨ x = 90
    · rcases present with rfl | rfl | rfl | rfl | rfl <;> cases shifted <;> rcases supported with rfl | rfl
      all_goals
        first
        | (change none = some t at typed; cases typed)
        | (change some (.int 32) = some t at typed; cases typed; cases lookup; rfl)
        | (change some (.int 64) = some t at typed; cases typed; cases lookup; rfl)
    · simp only [not_or] at present
      simp [frame,present.1,present.2.1,present.2.2.1,present.2.2.2.1,present.2.2.2.2] at lookup

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
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) && result.blockScans.toList.any (fun event =>
        decide (ctxKey event.ctx = ctxKey (built shifted ty).1) && event.output.records.any (fun record =>
          record.inst == index shifted && decide (record.output.state.demand = demand shifted) &&
          record.output.step.any (fun step => step.decision == .emitted && decide (step.rules.getLast? = some rule_lower_1406.id))))) = some true := by
  cases shifted <;> rcases supported with rfl | rfl <;> decide +kernel
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
  clif : info.clif = some (.unary .bnot ty 90)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg (resultKey shifted) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some rule_lower_1406.id
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
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,demand,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some rule_lower_1406.id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.unary .bnot ty 90),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      cases shifted <;> rcases supported with rfl | rfl <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.unary .bnot ty 90) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg (resultKey shifted) .int) := by
      simp only [Ctx.valueReg?,maps]
      cases shifted <;> rcases supported with rfl | rfl <;> rfl
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
          cases shifted <;> rcases supported with rfl | rfl <;> rfl
        · dsimp only
          rw [alias192]
          cases shifted <;> rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          change some (.ofInt ty 5) = some val at lookup
          cases lookup
          refine ⟨193,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            cases shifted <;> rcases supported with rfl | rfl <;> rfl
          · dsimp only
            rw [alias193]
            cases shifted <;> rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
        · by_cases unmaterialized : x = 64 ∨ x = 63 ∨ x = 90
          · rcases unmaterialized with rfl | rfl | rfl
            all_goals
              rw [Demanded,demand] at needed
              cases shifted <;> change 0 ≠ 0 at needed <;> exact False.elim (needed rfl)
          · simp only [not_or] at unmaterialized
            simp [frame,seven,thirtyone,unmaterialized.1,unmaterialized.2.1,unmaterialized.2.2] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,actualDFG,held⟩⟩

/-- At32/64 bits, actual complete NOT-of-XOR records establish the
original unary value without materializing the sunk XOR in machine
registers; only the fresh destination changes. -/
theorem stock_lower_not_xor_fused_record_values_witness (shifted : Bool) (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV),
      Stock.lower (function shifted ty) = .ok result ∧ LowerScope (function shifted ty) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bnot (BitVec.ofNat ty.width (sourceValue shifted))⟩
        (ρ' record.input.base.nextVreg) ∧ ∀ n, n ≠ record.input.base.nextVreg → ρ' n = regs n := by
  obtain ⟨input⟩ := inputs shifted ty supported
  have get : (frame shifted ty).getAs 90 ty =
      .ok (BitVec.ofNat ty.width (sourceValue shifted)) := by
    cases shifted <;> rcases supported with rfl | rfl <;> rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_not_xor_record_values
    input.run (scope shifted ty supported) input.events input.records input.source input.clif input.results
    input.mapped input.recorded input.emitted input.selectedId self input.dfg input.held get
  exact ⟨input.result,input.event,input.record,ρ',input.run,scope shifted ty supported,input.events,input.records,execution,value,kept⟩

private theorem dominated (shifted : Bool) (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) : Dominated (function shifted ty) := by
  constructor
  · cases shifted
    · change ([7,31,64,90,100] : List Nat).Nodup; decide +kernel
    · change ([7,31,64,63,90,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function] at block
      subst b
      constructor
      · intro j stm statement y member
        cases shifted
        · cases j with
          | zero => simp at statement; subst stm; cases member
          | succ j =>
            cases j with
            | zero =>
              simp at statement; subst stm
              change y ∈ [7,64] at member
              simp only [List.mem_cons,List.not_mem_nil,or_false] at member
              rcases member with rfl | rfl <;> simp [availOf,function,operand,constant,defsBefore,defsFrom]
            | succ j =>
              cases j <;> simp at statement; subst stm
              change y ∈ [90] at member
              have equal := List.mem_singleton.mp member; subst y
              simp [availOf,function,operand,constant,defsBefore,defsFrom]
        · cases j with
          | zero => simp at statement; subst stm; cases member
          | succ j =>
            cases j with
            | zero =>
              simp at statement; subst stm
              change y ∈ [31,64] at member
              simp only [List.mem_cons,List.not_mem_nil,or_false] at member
              rcases member with rfl | rfl <;> simp [availOf,function,operand,constant,defsBefore,defsFrom]
            | succ j =>
              cases j with
              | zero =>
                simp at statement; subst stm
                change y ∈ [7,63] at member
                simp only [List.mem_cons,List.not_mem_nil,or_false] at member
                rcases member with rfl | rfl <;> simp [availOf,function,operand,constant,defsBefore,defsFrom]
              | succ j =>
                cases j <;> simp at statement; subst stm
                change y ∈ [90] at member
                have equal := List.mem_singleton.mp member; subst y
                simp [availOf,function,operand,constant,defsBefore,defsFrom]
      · intro y member
        have narrowed : y ∈ [100] := by cases shifted <;> rcases supported with rfl | rfl <;> exact member
        have equal := List.mem_singleton.mp narrowed; subst y
        cases shifted <;> simp [availOf,function,operand,constant,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function shifted ty) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function shifted ty).blocks.length = 1 := rfl
    omega

private theorem frame_available (shifted : Bool) (ty : Clif.Ty) (ctx : Ctx) :
    (restrict (frame shifted ty) (availOf (function shifted ty) (availIn (function shifted ty) ctx) 0 (index shifted))).regs = (frame shifted ty).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31 ∨ x = 64 ∨ x = 63 ∨ x = 90
  · rcases present with rfl | rfl | rfl | rfl | rfl
    · apply restrict_regs_of_mem; cases shifted <;> simp [availOf,function,operand,constant,index,defsBefore,defsFrom]
    · apply restrict_regs_of_mem; cases shifted <;> simp [availOf,function,operand,constant,index,defsBefore,defsFrom]
    · apply restrict_regs_of_mem; cases shifted <;> simp [availOf,function,operand,constant,index,defsBefore,defsFrom]
    · cases shifted
      · simp [restrict,frame]
      · apply restrict_regs_of_mem; simp [availOf,function,operand,constant,index,defsBefore,defsFrom]
    · apply restrict_regs_of_mem; cases shifted <;> simp [availOf,function,operand,constant,index,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2.1,present.2.2.1,present.2.2.2.1,present.2.2.2.2]

/-- Actual NOT-of-XOR source steps inhabit the availability guard and
transfer into the real resulting source frame at32/64 bits. -/
theorem stock_lower_not_xor_fused_source_values_witness (shifted : Bool) (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function shifted ty) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs ρ' ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame shifted ty,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (function shifted ty) (availIn (function shifted ty) result.ctx) 0 ((index shifted)+1))
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := inputs shifted ty supported
  have get : (frame shifted ty).getAs 90 ty =
      .ok (BitVec.ofNat ty.width (sourceValue shifted)) := by
    cases shifted <;> rcases supported with rfl | rfl <;> rfl
  have restrictedGet := getAs_congr (fr := frame shifted ty) (x := 90) (ty := ty)
    (congrFun (frame_available shifted ty input.result.ctx) 90)
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := frame shifted ty)
    (fr' := restrict (frame shifted ty) (availOf (function shifted ty) (availIn (function shifted ty) input.result.ctx) 0 (index shifted)))
    rfl rfl (frame_available shifted ty input.result.ctx) input.dfg
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (function shifted ty) (availIn (function shifted ty) input.result.ctx) 0 (index shifted)) => h.1)
  have block : (function shifted ty).blocks[0]? = some ((function shifted ty).blocks[0]!) := rfl
  have statement : ((function shifted ty).blocks[0]!).body[(index shifted)]? =
      some (⟨[100],.unary .bnot ty 90⟩ : Clif.Stmt) := by cases shifted <;> rfl
  have current : input.record.inst = blockStart (function shifted ty) 0 + (index shifted) := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨ρ',execution,value,kept,installed⟩ := stock_lower_not_xor_available_values input.run (scope shifted ty supported)
    (dominated shifted ty supported) input.events input.records block statement current input.source input.clif input.results rfl
    input.mapped input.recorded input.emitted input.selectedId self restrictedDFG guarded (restrictedGet.trans get)
  let val : Clif.Val := ⟨ty,Clif.Sem.unary .bnot (BitVec.ofNat ty.width (sourceValue shifted))⟩
  let fr' : Clif.Frame := {frame shifted ty with regs := (frame shifted ty).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame shifted ty) Clif.Mem.empty
      (.unary .bnot ty 90) = .ok ([val],Clif.Mem.empty) := by
    cases shifted <;> rcases supported with rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame shifted ty,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.unary .bnot ty 90,[val],(frame shifted ty).regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have sourceHeld := source_single_result_values input.source input.clif input.results sourceStep evaluated installed
  exact ⟨input.result,input.event,input.record,ρ',fr',input.run,input.events,input.records,execution,sourceStep,sourceHeld⟩

end Backend.Stock.Proof.LogicalNot.XorFusedWitness
