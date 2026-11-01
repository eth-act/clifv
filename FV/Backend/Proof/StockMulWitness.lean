import FV.Backend.Proof.StockMulRecordValues
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.ScalarMul.Witness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def function (ty : Clif.Ty) : Clif.Function := {
  name := "stock_mul_values"
  sig := {params := [⟨ty,.none,.normal⟩,⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty),(31,ty)],body :=
    [⟨[100],.binary .imul ty 7 31⟩],term := .ret [100]}] }
private def built (ty : Clif.Ty) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function ty)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (ty : Clif.Ty) : Clif.Frame := {
  func := function ty
  regs := fun x => if x = 7 then some (.ofInt ty 7) else
    if x = 31 then some (.ofInt ty 5) else none
  slots := [],body := [⟨[100],.binary .imul ty 7 31⟩],term := .ret [100] }
private def regs (n : Nat) : CV := if n = 192 then 7 else if n = 193 then 5 else 0
private def demand : Array Nat := (Array.replicate 101 0).modify 7 (·+1) |>.modify 31 (·+1) |>.modify 100 (·+1)
private theorem scope (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) : LowerScope (function ty) :=
  lowerScope_of (by rcases supported with rfl | rfl <;> decide +kernel)
private def sourceKey (info : IInfo) := (info.clif,info.results)
private def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)

section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) :
    (Stock.lower (function ty)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) && result.blockScans.toList.any (fun event =>
        decide (ctxKey event.ctx = ctxKey (built ty).1) && event.output.records.any (fun record =>
          record.inst == (0 : Nat) && decide (record.output.state.demand = demand) &&
          record.output.step.any (fun step => step.decision == .emitted && decide (step.rules.getLast? = some rule_lower_871.id))))) = some true := by
  rcases supported with rfl | rfl <;> decide +kernel
end Runs

private structure Inputs (ty : Clif.Ty) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function ty) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = (0 : Nat)
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.binary .imul ty 7 31)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some rule_lower_871.id
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty)
    (fun k => regs (aliasNum result.final.alias k))

private theorem inputs (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) :
    Nonempty (Inputs ty) := by
  have actual := observed ty supported
  cases run : Stock.lower (function ty) with
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
          step.rules.getLast? = some rule_lower_871.id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.binary .imul ty 7 31),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      rcases supported with rfl | rfl <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.binary .imul ty 7 31) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg ((194 : Nat)) .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty)
        (fun n => regs (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt ty 7) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rcases supported with rfl | rfl <;> rfl
        · dsimp only
          rw [alias192]
          rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          change some (.ofInt ty 5) = some val at lookup
          cases lookup
          refine ⟨193,?_,?_⟩
          · simp only [Ctx.valueReg?,maps]
            rcases supported with rfl | rfl <;> rfl
          · dsimp only
            rw [alias193]
            rcases supported with rfl | rfl <;> unfold VHolds <;> decide +kernel
        · simp [frame,seven,thirtyone] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,held⟩⟩

/-- At32/64 bits, actual complete multiplication records establish the
original unary value without materializing the source operands in machine
registers; only the fresh destination changes. -/
theorem stock_lower_mul_record_values_witness (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV),
      Stock.lower (function ty) = .ok result ∧ LowerScope (function ty) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary .imul (BitVec.ofNat ty.width 7) (BitVec.ofNat ty.width 5)⟩
        (ρ' record.input.base.nextVreg) ∧ ∀ n, n ≠ record.input.base.nextVreg → ρ' n = regs n := by
  obtain ⟨input⟩ := inputs ty supported
  have getX : (frame ty).getAs 7 ty = .ok (BitVec.ofNat ty.width 7) := by
    rcases supported with rfl | rfl <;> rfl
  have getY : (frame ty).getAs 31 ty = .ok (BitVec.ofNat ty.width 5) := by
    rcases supported with rfl | rfl <;> rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_mul_record_values
    input.run (scope ty supported) input.events input.records input.source input.clif input.results
    input.mapped input.recorded input.emitted input.selectedId self input.held getX getY
  exact ⟨input.result,input.event,input.record,ρ',input.run,scope ty supported,input.events,input.records,execution,value,kept⟩

private theorem dominated (ty : Clif.Ty) (supported : ty = .i32 ∨ ty = .i64) : Dominated (function ty) := by
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
        have narrowed : y ∈ [100] := by rcases supported with rfl | rfl <;> exact member
        have equal := List.mem_singleton.mp narrowed
        clear member narrowed
        subst y
        simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function ty) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function ty).blocks.length = 1 := rfl
    omega

private theorem frame_available (ty : Clif.Ty) (ctx : Ctx) :
    (restrict (frame ty) (availOf (function ty) (availIn (function ty) ctx) 0 0)).regs = (frame ty).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]

/-- Actual multiplication source steps inhabit the availability guard and
transfer into the real resulting source frame at32/64 bits. -/
theorem stock_lower_mul_source_values_witness (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function ty) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs ρ' ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame ty,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (function ty) (availIn (function ty) result.ctx) 0 ((0 : Nat)+1))
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := inputs ty supported
  have getX : (frame ty).getAs 7 ty = .ok (BitVec.ofNat ty.width 7) := by
    rcases supported with rfl | rfl <;> rfl
  have getY : (frame ty).getAs 31 ty = .ok (BitVec.ofNat ty.width 5) := by
    rcases supported with rfl | rfl <;> rfl
  have restrictedX := getAs_congr (fr := frame ty) (x := 7) (ty := ty)
    (congrFun (frame_available ty input.result.ctx) 7)
  have restrictedY := getAs_congr (fr := frame ty) (x := 31) (ty := ty)
    (congrFun (frame_available ty input.result.ctx) 31)
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (function ty) (availIn (function ty) input.result.ctx) 0 ((0 : Nat))) => h.1)
  have block : (function ty).blocks[0]? = some ((function ty).blocks[0]!) := rfl
  have statement : ((function ty).blocks[0]!).body[(0 : Nat)]? =
      some (⟨[100],.binary .imul ty 7 31⟩ : Clif.Stmt) := by rfl
  have current : input.record.inst = blockStart (function ty) 0 + (0 : Nat) := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨ρ',execution,value,kept,installed⟩ := stock_lower_mul_available_values input.run (scope ty supported)
    (dominated ty supported) input.events input.records block statement current input.source input.clif input.results rfl
    input.mapped input.recorded input.emitted input.selectedId self guarded (restrictedX.trans getX) (restrictedY.trans getY)
  let val : Clif.Val := ⟨ty,Clif.Sem.binary .imul (BitVec.ofNat ty.width 7) (BitVec.ofNat ty.width 5)⟩
  let fr' : Clif.Frame := {frame ty with regs := (frame ty).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame ty) Clif.Mem.empty
      (.binary .imul ty 7 31) = .ok ([val],Clif.Mem.empty) := by
    rcases supported with rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame ty,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.binary .imul ty 7 31,[val],(frame ty).regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have sourceHeld := source_single_result_values input.source input.clif input.results sourceStep evaluated installed
  exact ⟨input.result,input.event,input.record,ρ',fr',input.run,input.events,input.records,execution,sourceStep,sourceHeld⟩

end Backend.Stock.Proof.ScalarMul.Witness
