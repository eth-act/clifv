import FV.Backend.Proof.StockUnarySourceValues
import FV.Backend.Proof.LowerValueRelations
namespace Backend.Stock.Proof.ScalarBit.BswapWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def rootIndex (aliased : Bool) : Nat := if aliased then 1 else 0
private def instruction (ty : Clif.Ty) : Clif.Inst := .unary .bswap ty 7
private def function (ty : Clif.Ty) (aliased : Bool) : Clif.Function := {
  name := "stock_bswap_source_values"
  sig := {params := (if aliased then [] else [⟨ty,.none,.normal⟩]),returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := (if aliased then [] else [(7,ty)]),body :=
    (if aliased then [⟨[7],.iconst ty (BitVec.ofInt ty.width (-91))⟩] else []) ++ [⟨[100],instruction ty⟩],term := .ret [100]}] }
private def built (ty : Clif.Ty) (aliased : Bool) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function ty aliased)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (ty : Clif.Ty) (aliased : Bool) : Clif.Frame := {
  func := function ty aliased,regs := fun x => if x = 7 then some (.ofInt ty (-91)) else none,
  slots := [],body := [⟨[100],instruction ty⟩],term := .ret [100] }
private def regs (ty : Clif.Ty) (aliased : Bool) (n : Nat) : CV :=
  if n = (if aliased then 195 else 192) then BitVec.ofNat 128 (2^100+2^ty.width+(Clif.Val.ofInt ty (-91)).bits.toNat) else 0
private def demand : Array Nat := (Array.replicate 101 0).modify 7 (·+1) |>.modify 100 (·+1)
private def sourceKey (info : IInfo) := (info.clif,info.results)
private def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
private theorem scope (ty : Clif.Ty) (aliased : Bool)
    (supported : ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : LowerScope (function ty aliased) :=
  lowerScope_of (by cases aliased <;> rcases supported with rfl | rfl | rfl <;> decide +kernel)

section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private def observedReport (ty : Clif.Ty) (aliased : Bool) : Option Bool :=
  (Stock.lower (function ty aliased)).toOption.map (fun result =>
    decide (aliasNum result.final.alias 192 = if aliased then 195 else 192) && result.blockScans.toList.any (fun event =>
      decide (ctxKey event.ctx = ctxKey (built ty aliased).1) && event.output.records.any (fun record =>
        record.inst == rootIndex aliased && decide (record.output.state.demand = demand) &&
        record.input.base.nextVreg == 194 && record.output.step.any (fun step => step.decision == .emitted &&
          decide (step.rules.getLast? = some (bswapRule ty.width).id)))))
private theorem observed_i16_false : observedReport .i16 false = some true := by decide +kernel
private theorem observed_i16_true : observedReport .i16 true = some true := by decide +kernel
private theorem observed_i32_false : observedReport .i32 false = some true := by decide +kernel
private theorem observed_i32_true : observedReport .i32 true = some true := by decide +kernel
private theorem observed_i64_false : observedReport .i64 false = some true := by decide +kernel
private theorem observed_i64_true : observedReport .i64 true = some true := by decide +kernel
private theorem observed (ty : Clif.Ty) (aliased : Bool) (supported : ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : observedReport ty aliased = some true := by
  cases aliased <;> rcases supported with rfl | rfl | rfl
  · exact observed_i16_false
  · exact observed_i32_false
  · exact observed_i64_false
  · exact observed_i16_true
  · exact observed_i32_true
  · exact observed_i64_true
end Runs

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
  mapped : event.ctx.valueReg? 100 = some (.vreg 193 .int)
  sourceMapped : event.ctx.valueReg? 7 = some (.vreg 192 .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (bswapRule ty.width).id
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty aliased)
    (fun k => regs ty aliased (aliasNum result.final.alias k))
private theorem inputs (ty : Clif.Ty) (aliased : Bool) (supported : ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : Nonempty (Inputs ty aliased) := by
  have actual := observed ty aliased supported
  unfold observedReport at actual
  cases run : Stock.lower (function ty aliased) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,event,events,ctxEq,record,records,current,demandEq,frontier,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some (bswapRule ty.width).id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey = some (some (instruction ty),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      rcases supported with rfl | rfl | rfl <;> cases aliased <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (instruction ty) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 193 .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl | rfl <;> cases aliased <;> rfl
    have sourceMapped : event.ctx.valueReg? 7 = some (.vreg 192 .int) := by
      simp only [Ctx.valueReg?,maps]
      rcases supported with rfl | rfl | rfl <;> cases aliased <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame ty aliased)
        (fun k => regs ty aliased (aliasNum result.final.alias k)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt ty (-91)) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          rcases supported with rfl | rfl | rfl <;> cases aliased <;> rfl
        · dsimp only; rw [alias192]
          rcases supported with rfl | rfl | rfl <;> cases aliased <;> unfold VHolds <;> decide +kernel
      · simp [frame,seven] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,sourceMapped,
      recorded,emitted,selectedId,held⟩⟩
private theorem dominated (ty : Clif.Ty) (aliased : Bool) (supported : ty = .i16 ∨ ty = .i32 ∨ ty = .i64) : Dominated (function ty aliased) := by
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
        have narrowed : v ∈ [100] := by rcases supported with rfl | rfl | rfl <;> cases aliased <;> exact member
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
  · simp [restrict,frame,seven]
/-- All three supported scalar widths have actual complete source/record witnesses,
including earlier-producer reads through final aliases with unmaterialized
original source registers and dirty upper machine bits. -/
theorem stock_lower_bswap_source_values_witness (ty : Clif.Ty) (aliased : Bool)
    (supported : ty = .i16 ∨ ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function ty aliased) = .ok result ∧ LowerScope (function ty aliased) ∧ Dominated (function ty aliased) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧
      step.rules.getLast? = some (bswapRule ty.width).id ∧ step.results = [[.vreg d .int]] ∧
      (record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg) ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs ty aliased) ρ' ∧
      VHolds ⟨ty,Clif.Sem.unary .bswap (BitVec.ofInt ty.width (-91))⟩ (ρ' d) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (frame ty aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf (function ty aliased) (availIn (function ty aliased) result.ctx) 0 (rootIndex aliased+1)) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) ∧
      (aliased = true → regs ty aliased 192 = 0) := by
  obtain ⟨input⟩ := inputs ty aliased supported
  have sameFrame := frame_available ty aliased input.result.ctx
  have getX : (restrict (frame ty aliased) (availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0
      (rootIndex aliased))).getAs 7 ty = .ok (BitVec.ofInt ty.width (-91)) := by
    have original : (frame ty aliased).getAs 7 ty = .ok (BitVec.ofInt ty.width (-91)) := by
      rcases supported with rfl | rfl | rfl <;> rfl
    exact (getAs_congr (fr := frame ty aliased) (x := 7) (ty := ty) (congrFun sameFrame 7)).trans original
  have guarded := input.held.mono (fun v (h : Demanded input.record.output.state v ∧
      v ∈ availOf (function ty aliased) (availIn (function ty aliased) input.result.ctx) 0 (rootIndex aliased)) => h.1)
  let val : Clif.Val := ⟨ty,Clif.Sem.unary .bswap (BitVec.ofInt ty.width (-91))⟩
  let fr' : Clif.Frame := {frame ty aliased with regs := (frame ty aliased).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame ty aliased) Clif.Mem.empty (instruction ty) =
      .ok ([val],Clif.Mem.empty) := by rcases supported with rfl | rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame ty aliased,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,instruction ty,[val],(frame ty aliased).regs.set 100 val,[],input.source,input.clif,
      by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have block : (function ty aliased).blocks[0]? = some ((function ty aliased).blocks[0]!) := rfl
  have statement : ((function ty aliased).blocks[0]!).body[rootIndex aliased]? = some (⟨[100],instruction ty⟩ : Clif.Stmt) := by
    cases aliased <;> rfl
  have current : input.record.inst = blockStart (function ty aliased) 0 + rootIndex aliased := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨actual,d,ρ',found,output,bounds,execution,value,memEq,kept,post⟩ := stock_lower_bswap_source_from_step input.run
    (scope ty aliased supported) (dominated ty aliased supported) input.events input.records block statement current
    input.source input.clif input.results rfl input.mapped input.recorded input.emitted input.selectedId self guarded sourceStep
  have actualEq := Clif.Res.ok.inj (found.symm.trans getX)
  subst actual
  exact ⟨input.result,input.event,input.record,input.step,d,ρ',fr',input.run,scope ty aliased supported,dominated ty aliased supported,
    input.events,input.records,input.recorded,input.emitted,input.selectedId,output,bounds,execution,value,sourceStep,post,fun yes => by
      subst aliased
      have separate : (192 : Nat) ≠ 195 := by omega
      simp [regs,separate]⟩

end Backend.Stock.Proof.ScalarBit.BswapWitness
