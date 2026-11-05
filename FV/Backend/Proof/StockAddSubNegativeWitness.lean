import FV.Backend.Proof.StockAddSubAllSourceValues
import FV.Backend.Proof.LowerValueRelations
namespace Backend.Stock.Proof.ScalarAddSub.NegativeWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
inductive Kind where
  | addRight | addLeft | subRight
  deriving DecidableEq
def Kind.subtract : Kind → Bool | .subRight => true | _ => false
def Kind.left : Kind → Bool | .addLeft => true | _ => false
def Kind.cop (kind : Kind) : Clif.BinaryOp := if kind.subtract then .isub else .iadd
def Kind.rule (kind : Kind) (ty : Clif.Ty) : Rule :=
  if ty = .i8 ∧ kind.subtract = false then immRule kind.subtract kind.left else negImmRule kind.subtract kind.left
private def instruction (kind : Kind) (ty : Clif.Ty) : Clif.Inst :=
  .binary kind.cop ty (if kind.left then 31 else 7) (if kind.left then 7 else 31)
private def function (kind : Kind) (ty : Clif.Ty) : Clif.Function := {
  name := "stock_addsub_negative_complete"
  sig := {params := [⟨ty,.none,.normal⟩],returns := [⟨ty,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(7,ty)],body := [⟨[31],.iconst ty (BitVec.ofInt ty.width (-5))⟩,
    ⟨[100],instruction kind ty⟩],term := .ret [100]}] }
private def built (kind : Kind) (ty : Clif.Ty) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (function kind ty)).toOption.getD (sinkCtx,#[],sinkState)
private def frame (kind : Kind) (ty : Clif.Ty) : Clif.Frame := {
  func := function kind ty
  regs := fun x => if x = 7 then some (.ofInt ty 7) else if x = 31 then some (.ofInt ty (-5)) else none
  slots := [],body := [⟨[100],instruction kind ty⟩],term := .ret [100] }
private def regs (ty : Clif.Ty) (n : Nat) : CV := if n = 192 then BitVec.ofNat 128 (2^100+2^ty.width+7) else 0
private def demand : Array Nat := (Array.replicate 101 0).modify 7 (·+1) |>.modify 100 (·+1)
private def sourceKey (info : IInfo) := (info.clif,info.results)
private def ctxKey (ctx : Ctx) := (ctx.insts.map sourceKey,ctx.valTy,ctx.valDef,ctx.valReg)
private def Supported (ty : Clif.Ty) := ty = .i8 ∨ ty = .i16 ∨ ty = .i32 ∨ ty = .i64
private theorem scope (kind : Kind) (ty : Clif.Ty) (supported : Supported ty) : LowerScope (function kind ty) :=
  lowerScope_of (by cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel)
section Runs
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private def observedReport (kind : Kind) (ty : Clif.Ty) : Option Bool :=
  (Stock.lower (function kind ty)).toOption.map (fun result =>
    decide (aliasNum result.final.alias 192 = 192 ∧ aliasNum result.final.alias 193 = 193) && result.blockScans.toList.any (fun event =>
      decide (ctxKey event.ctx = ctxKey (built kind ty).1) && event.output.records.any (fun record =>
        record.inst == 1 && decide (record.output.state.demand = demand) && record.input.base.nextVreg == 195 &&
        record.output.step.any (fun step => step.decision == .emitted &&
          decide (step.rules.getLast? = some (kind.rule ty).id ∧ step.results = [[.vreg 195 .int]])))))
private theorem observed_addRight_8 : observedReport .addRight .i8 = some true := by decide +kernel
private theorem observed_addRight_16 : observedReport .addRight .i16 = some true := by decide +kernel
private theorem observed_addRight_32 : observedReport .addRight .i32 = some true := by decide +kernel
private theorem observed_addRight_64 : observedReport .addRight .i64 = some true := by decide +kernel
private theorem observed_addLeft_8 : observedReport .addLeft .i8 = some true := by decide +kernel
private theorem observed_addLeft_16 : observedReport .addLeft .i16 = some true := by decide +kernel
private theorem observed_addLeft_32 : observedReport .addLeft .i32 = some true := by decide +kernel
private theorem observed_addLeft_64 : observedReport .addLeft .i64 = some true := by decide +kernel
private theorem observed_subRight_8 : observedReport .subRight .i8 = some true := by decide +kernel
private theorem observed_subRight_16 : observedReport .subRight .i16 = some true := by decide +kernel
private theorem observed_subRight_32 : observedReport .subRight .i32 = some true := by decide +kernel
private theorem observed_subRight_64 : observedReport .subRight .i64 = some true := by decide +kernel
private theorem observed (kind : Kind) (ty : Clif.Ty) (supported : Supported ty) : observedReport kind ty = some true := by
  cases kind <;> rcases supported with rfl | rfl | rfl | rfl
  · exact observed_addRight_8
  · exact observed_addRight_16
  · exact observed_addRight_32
  · exact observed_addRight_64
  · exact observed_addLeft_8
  · exact observed_addLeft_16
  · exact observed_addLeft_32
  · exact observed_addLeft_64
  · exact observed_subRight_8
  · exact observed_subRight_16
  · exact observed_subRight_32
  · exact observed_subRight_64
end Runs
private theorem dfg_base (kind : Kind) (ty : Clif.Ty) (supported : Supported ty) : DFGCons (built kind ty).1 (frame kind ty) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases seven : x = 7
    · subst x
      have absent : (built kind ty).1.defInst? 7 = none := by cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
      rw [absent] at defined; cases defined
    · by_cases literal : x = 31
      · subst x
        cases kind <;> rcases supported with rfl | rfl | rfl | rfl
        all_goals
          change some 0 = some j at defined
          cases defined
          obtain ⟨bound,equal⟩ := Array.getElem?_eq_some_iff.mp found
          subst info
          cases original
          cases lookup
          exact ⟨[_],fun cm => rfl,rfl⟩
      · simp [frame,seven,literal] at lookup
  · intro x t v typed lookup
    by_cases present : x = 7 ∨ x = 31
    · rcases present with rfl | rfl <;> cases kind <;> rcases supported with rfl | rfl | rfl | rfl
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
private structure Inputs (kind : Kind) (ty : Clif.Ty) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function kind ty) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = 1
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (instruction kind ty)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some (kind.rule ty).id
  outputs : step.results = [[.vreg 195 .int]]
  frontier : record.input.base.nextVreg = 195
  dfg : DFGCons event.ctx (frame kind ty)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame kind ty) (fun k => regs ty (aliasNum result.final.alias k))
private theorem inputs (kind : Kind) (ty : Clif.Ty) (supported : Supported ty) : Nonempty (Inputs kind ty) := by
  have actual := observed kind ty supported
  unfold observedReport at actual
  cases run : Stock.lower (function kind ty) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,demandEq,frontier,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId,outputs⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,and_assoc] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some (kind.rule ty).id ∧
          step.results = [[.vreg 195 .int]])
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey = some (some (instruction kind ty),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (instruction kind ty) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 194 .int) := by
      simp only [Ctx.valueReg?,maps]
      cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame kind ty)
        (fun k => regs ty (aliasNum result.final.alias k)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt ty 7) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,maps]
          cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
        · dsimp only; rw [alias192]
          rcases supported with rfl | rfl | rfl | rfl <;> unfold VHolds <;> decide +kernel
      · by_cases literal : x = 31
        · subst x
          unfold Demanded at needed
          rw [demandEq] at needed
          change (0 : Nat) ≠ 0 at needed
          exact (needed rfl).elim
        · simp [frame,seven,literal] at lookup
    have dfg := dfg_transport insts types defs (dfg_base kind ty supported)
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,outputs,frontier,dfg,held⟩⟩
private theorem dominated (kind : Kind) (ty : Clif.Ty) (supported : Supported ty) : Dominated (function kind ty) := by
  constructor
  · change ([7,31,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b block
    cases bi with
    | zero =>
      simp [function] at block
      subst b
      constructor
      · intro j stm statement v member
        cases j
        · simp at statement; subst stm; cases member
        · rename_i j
          cases j <;> simp at statement
          subst stm
          cases kind
          all_goals change v ∈ [_,_] at member
          all_goals simp only [List.mem_cons,List.not_mem_nil,or_false,Kind.left,Bool.false_eq_true,ite_false,ite_true] at member
          all_goals rcases member with rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
      · intro v member
        have narrowed : v ∈ [100] := by cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> exact member
        have equal := List.mem_singleton.mp narrowed
        subst v
        simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at block
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function kind ty) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function kind ty).blocks.length = 1 := rfl
    omega
private theorem frame_available (kind : Kind) (ty : Clif.Ty) (ctx : Ctx) :
    (restrict (frame kind ty) (availOf (function kind ty) (availIn (function kind ty) ctx) 0 1)).regs = (frame kind ty).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31
  · rcases present with rfl | rfl <;> apply restrict_regs_of_mem <;> simp [availOf,function,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2]
/-- All negative-immediate forms, including original i8 add precedence, have
actual complete original source/record witnesses. At i8, add uses its higher-priority positive-immediate root; subtraction
uses its negative root. The looked-through constant
register is absent and the held operand has dirty upper bits. -/
theorem stock_lower_addsub_negative_source_witness (kind : Kind) (ty : Clif.Ty) (supported : Supported ty) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (function kind ty) = .ok result ∧ LowerScope (function kind ty) ∧ Dominated (function kind ty) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some (kind.rule ty).id ∧
      step.results = [[.vreg 195 .int]] ∧ record.input.base.nextVreg = 195 ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (regs ty) ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop (BitVec.ofInt ty.width (if kind.left then (-5) else 7))
        (BitVec.ofInt ty.width (if kind.left then 7 else (-5)))⟩ (ρ' 195) ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame kind ty,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun v => Demanded record.input v ∧
        v ∈ availOf (function kind ty) (availIn (function kind ty) result.ctx) 0 2) event.ctx fr'
        (fun k => ρ' (aliasNum result.final.alias k)) ∧ regs ty 193 = 0 := by
  obtain ⟨input⟩ := inputs kind ty supported
  have sameFrame := frame_available kind ty input.result.ctx
  have guarded := input.held.mono (fun v (h : Demanded input.record.output.state v ∧
      v ∈ availOf (function kind ty) (availIn (function kind ty) input.result.ctx) 0 1) => h.1)
  let u := BitVec.ofInt ty.width (if kind.left then (-5) else 7)
  let v := BitVec.ofInt ty.width (if kind.left then 7 else (-5))
  let val : Clif.Val := ⟨ty,Clif.Sem.binary kind.cop u v⟩
  let fr' : Clif.Frame := {frame kind ty with regs := (frame kind ty).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame kind ty) Clif.Mem.empty (instruction kind ty) =
      .ok ([val],Clif.Mem.empty) := by cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame kind ty,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,instruction kind ty,[val],(frame kind ty).regs.set 100 val,[],input.source,input.clif,
      by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  have block : (function kind ty).blocks[0]? = some ((function kind ty).blocks[0]!) := rfl
  have statement : ((function kind ty).blocks[0]!).body[1]? = some (⟨[100],instruction kind ty⟩ : Clif.Stmt) := rfl
  have current : input.record.inst = blockStart (function kind ty) 0 + 1 := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := frame kind ty)
    (fr' := restrict (frame kind ty) (availOf (function kind ty) (availIn (function kind ty) input.result.ctx) 0 1)) rfl rfl sameFrame input.dfg
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have clif : input.info.clif = some (.binary (if kind.subtract then .isub else .iadd) ty
      (if kind.left then 31 else 7) (if kind.left then 7 else 31)) := input.clif
  obtain ⟨actualX,actualY,ρ',foundX,foundY,execution,value,memEq,kept,post⟩ := stock_lower_addsub_source_by_instruction
    input.run (scope kind ty supported) (dominated kind ty supported) input.events input.records block statement current
    kind.subtract input.source clif input.results rfl input.mapped input.recorded input.emitted self restrictedDFG guarded sourceStep
  have originalX : (frame kind ty).getAs (if kind.left then 31 else 7) ty = .ok u := by
    cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have originalY : (frame kind ty).getAs (if kind.left then 7 else 31) ty = .ok v := by
    cases kind <;> rcases supported with rfl | rfl | rfl | rfl <;> rfl
  have getX := (getAs_congr (fr := frame kind ty) (x := if kind.left then 31 else 7) (ty := ty)
    (congrFun sameFrame _)).trans originalX
  have getY := (getAs_congr (fr := frame kind ty) (x := if kind.left then 7 else 31) (ty := ty)
    (congrFun sameFrame _)).trans originalY
  have sameX := Clif.Res.ok.inj (foundX.symm.trans getX)
  have sameY := Clif.Res.ok.inj (foundY.symm.trans getY)
  subst actualX; subst actualY
  rw [input.frontier] at value
  exact ⟨input.result,input.event,input.record,input.step,ρ',fr',input.run,scope kind ty supported,dominated kind ty supported,
    input.events,input.records,input.recorded,input.emitted,input.selectedId,input.outputs,input.frontier,execution,value,sourceStep,post,rfl⟩
end Backend.Stock.Proof.ScalarAddSub.NegativeWitness
