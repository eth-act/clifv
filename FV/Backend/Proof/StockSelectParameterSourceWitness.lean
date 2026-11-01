import FV.Backend.Proof.StockSelectScanRefines
import FV.Backend.Proof.StockSelectScalarDriverRuns
import FV.Backend.Proof.StockSelectParameterDerivedSourceValues
import FV.Backend.Proof.LowerValueRelations
namespace Backend.Stock.Proof.ScalarSelect.ParameterSourceWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
structure Case where
  cty : Clif.Ty
  ty : Clif.Ty
  conditionWidth : cty.width = 8 ∨ cty.width = 16 ∨ cty.width = 32 ∨ cty.width = 64
  width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64
  cint : cty.isInt = true
  int : ty.isInt = true
private abbrev function (p : Case) := scalarSelectFunction p.cty p.ty
private abbrev built (p : Case) := scalarSelectBuilt p.cty p.ty
private def frame (p : Case) (word : BitVec p.cty.width) : Clif.Frame := {
  func := function p
  regs := fun x => if x = 7 then some ⟨p.cty,word⟩ else if x = 31 then some ⟨p.ty,7⟩ else if x = 63 then some ⟨p.ty,9⟩ else none
  slots := [],body := [⟨[100],.select p.ty 7 31 63⟩],term := .ret [100] }
private def registers (p : Case) (word : BitVec p.cty.width) (key : Nat) : CV :=
  if key = 192 then BitVec.ofNat 128 (2^100+word.toNat)
  else BitVec.ofNat 128 (2^100+if key = 193 then 7 else 9)
private theorem scope (p : Case) : LowerScope (function p) := by
  apply lowerScope_of
  rcases p with ⟨cty,ty,hc,ht,ci,ti⟩
  cases cty <;> cases ty <;> simp [Clif.Ty.width] at hc ht ci ti <;> rfl
private theorem dirty_word (ty : Clif.Ty) (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (word : BitVec ty.width) : (BitVec.ofNat 128 (2^100+word.toNat)).setWidth ty.width = word := by
  have bound : ty.width ≤ 128 := by omega
  have high : 2^100 % 2^ty.width = 0 := by rcases width with h | h | h | h <;> rw [h] <;> decide +kernel
  rw [BitVec.setWidth_ofNat_of_le bound]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.add_mod,high,Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
private theorem absent (p : Case) (key : Nat) (present : key = 7 ∨ key = 31 ∨ key = 63) :
    (built p).1.defInst? key = none := by
  rcases present with rfl | rfl | rfl
  all_goals rcases p with ⟨cty,ty,hc,ht,ci,ti⟩
  all_goals cases cty <;> cases ty <;> simp [Clif.Ty.width] at hc ht ci ti <;> rfl
private theorem typed (p : Case) (key : Nat) (present : key = 7 ∨ key = 31 ∨ key = 63) :
    (built p).1.valueType? key = some (.int (if key = 7 then p.cty.width else p.ty.width)) := by
  rcases present with rfl | rfl | rfl
  all_goals rcases p with ⟨cty,ty,hc,ht,ci,ti⟩
  all_goals cases cty <;> cases ty <;> simp [Clif.Ty.width] at hc ht ci ti <;> rfl
private theorem mapped_base (p : Case) (key : Nat) (present : key = 7 ∨ key = 31 ∨ key = 63 ∨ key = 100) :
    (built p).1.valueReg? key = some (.vreg (if key = 7 then 192 else if key = 31 then 193 else if key = 63 then 194 else 195) .int) := by
  rcases present with rfl | rfl | rfl | rfl
  all_goals rcases p with ⟨cty,ty,hc,ht,ci,ti⟩
  all_goals cases cty <;> cases ty <;> simp [Clif.Ty.width] at hc ht ci ti
  all_goals dsimp only [built,Case.cty,Case.ty]
  all_goals decide +kernel
private theorem source_base (p : Case) :
    ((built p).1.insts[0]?).map minmaxSourceKey = some (some (.select p.ty 7 31 63),[100]) := by
  rcases p with ⟨cty,ty,hc,ht,ci,ti⟩
  cases cty <;> cases ty <;> simp [Clif.Ty.width] at hc ht ci ti
  all_goals dsimp only [built,Case.cty,Case.ty]
  all_goals rfl
private theorem getter {fr : Clif.Frame} {x : Nat} {ty : Clif.Ty} {bits : BitVec ty.width}
    (read : fr.regs x = some ⟨ty,bits⟩) : fr.getAs x ty = .ok bits := by
  unfold Clif.Frame.getAs Clif.Frame.get
  rw [read]
  simp [Clif.Res.ofOption]
private theorem dfg_base (p : Case) (word : BitVec p.cty.width) : DFGCons (built p).1 (frame p word) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases hc : x = 7
    · subst x; rw [absent p 7 (by simp)] at defined; cases defined
    · by_cases hx : x = 31
      · subst x; rw [absent p 31 (by simp)] at defined; cases defined
      · by_cases hy : x = 63
        · subst x; rw [absent p 63 (by simp)] at defined; cases defined
        · simp [frame,hc,hx,hy] at lookup
  · intro x t v type lookup
    by_cases hc : x = 7
    · subst x; rw [typed p 7 (by simp)] at type; cases type; cases lookup
      exact ofClif_int_width p.cint
    · by_cases hx : x = 31
      · subst x; rw [typed p 31 (by simp)] at type; cases type
        simp only [frame,show (31:Nat) ≠ 7 by decide,ite_false,ite_true,Option.some.injEq] at lookup
        subst v; exact ofClif_int_width p.int
      · by_cases hy : x = 63
        · subst x; rw [typed p 63 (by simp)] at type; cases type
          simp only [frame,show (63:Nat) ≠ 7 by decide,show (63:Nat) ≠ 31 by decide,ite_false,ite_true,Option.some.injEq] at lookup
          subst v; exact ofClif_int_width p.int
        · simp [frame,hc,hx,hy] at lookup
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
private structure Inputs (p : Case) (word : BitVec p.cty.width) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (function p) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = 0
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.select p.ty 7 31 63)
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg 195 .int)
  typedC : event.ctx.valueType? 7 = some (.int p.cty.width)
  parameter : event.ctx.defInst? 7 = none
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some rule_lower_2267.id
  dfg : DFGCons event.ctx (frame p word)
  held : ValuesHeld (Demanded record.output.state) event.ctx (frame p word)
    (fun key => registers p word (aliasNum result.final.alias key))
private theorem inputs (p : Case) (word : BitVec p.cty.width) : Nonempty (Inputs p word) := by
  have actual := stock_select_scalar_driver_observed p.cty p.ty p.conditionWidth p.width p.cint p.int
  unfold ScalarSelectObserved at actual
  cases run : Stock.lower (function p) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq,
      List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨aliasC,aliasX,aliasY,event,events,ctxEq,record,records,current,stepData⟩ := actual
    simp only [minmaxCtxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_2267.id)
    have keyAt : (event.ctx.insts[record.inst]?).map minmaxSourceKey = some (some (.select p.ty 7 31 63),[100]) := by
      rw [← Array.getElem?_map,insts,current,Array.getElem?_map]
      exact source_base p
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.select p.ty 7 31 63) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg 195 .int) := by
      simpa only [Ctx.valueReg?,maps,ite_true,ite_false,show (100:Nat) ≠ 7 by decide,show (100:Nat) ≠ 31 by decide,show (100:Nat) ≠ 63 by decide,show (31:Nat) ≠ 7 by decide,show (63:Nat) ≠ 7 by decide,show (63:Nat) ≠ 31 by decide] using mapped_base p 100 (by simp)
    have typedC : event.ctx.valueType? 7 = some (.int p.cty.width) := by
      simpa only [Ctx.valueType?,types,ite_true] using typed p 7 (by simp)
    have parameter : event.ctx.defInst? 7 = none := by simpa only [Ctx.defInst?,defs] using absent p 7 (by simp)
    have held : ValuesHeld (Demanded record.output.state) event.ctx (frame p word)
        (fun key => registers p word (aliasNum result.final.alias key)) := by
      intro x needed value lookup
      by_cases hc : x = 7
      · subst x
        simp only [frame,ite_true,Option.some.injEq] at lookup
        subst value
        refine ⟨192,?_,?_⟩
        · simpa only [Ctx.valueReg?,maps,ite_true,ite_false,show (100:Nat) ≠ 7 by decide,show (100:Nat) ≠ 31 by decide,show (100:Nat) ≠ 63 by decide,show (31:Nat) ≠ 7 by decide,show (63:Nat) ≠ 7 by decide,show (63:Nat) ≠ 31 by decide] using mapped_base p 7 (by simp)
        · dsimp only
          rw [aliasC]
          exact dirty_word p.cty p.conditionWidth word
      · by_cases hx : x = 31
        · subst x
          simp only [frame,show (31:Nat) ≠ 7 by decide,ite_false,ite_true,Option.some.injEq] at lookup
          subst value
          refine ⟨193,?_,?_⟩
          · simpa only [Ctx.valueReg?,maps,ite_true,ite_false,show (100:Nat) ≠ 7 by decide,show (100:Nat) ≠ 31 by decide,show (100:Nat) ≠ 63 by decide,show (31:Nat) ≠ 7 by decide,show (63:Nat) ≠ 7 by decide,show (63:Nat) ≠ 31 by decide] using mapped_base p 31 (by simp)
          · dsimp only
            rw [aliasX]
            change (BitVec.ofNat 128 (2^100+7)).setWidth p.ty.width = BitVec.ofNat p.ty.width 7
            rcases p.width with h | h | h | h <;> rw [h] <;> decide +kernel
        · by_cases hy : x = 63
          · subst x
            simp only [frame,show (63:Nat) ≠ 7 by decide,show (63:Nat) ≠ 31 by decide,ite_false,ite_true,Option.some.injEq] at lookup
            subst value
            refine ⟨194,?_,?_⟩
            · simpa only [Ctx.valueReg?,maps,ite_true,ite_false,show (100:Nat) ≠ 7 by decide,show (100:Nat) ≠ 31 by decide,show (100:Nat) ≠ 63 by decide,show (31:Nat) ≠ 7 by decide,show (63:Nat) ≠ 7 by decide,show (63:Nat) ≠ 31 by decide] using mapped_base p 63 (by simp)
            · dsimp only
              rw [aliasY]
              change (BitVec.ofNat 128 (2^100+9)).setWidth p.ty.width = BitVec.ofNat p.ty.width 9
              rcases p.width with h | h | h | h <;> rw [h] <;> decide +kernel
          · simp [frame,hc,hx,hy] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,typedC,parameter,
      recorded,emitted,selectedId,dfg_transport insts types defs (dfg_base p word),held⟩⟩
private theorem dominated (p : Case) : Dominated (function p) := by
  constructor
  · change ([7,31,63,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi block found
    cases bi with
    | zero =>
      simp [function,scalarSelectFunction] at found
      subst block
      constructor
      · intro j stmt statement x member
        cases j <;> simp at statement
        subst stmt
        change x ∈ [7,31,63] at member
        simp only [List.mem_cons,List.not_mem_nil,or_false] at member
        rcases member with rfl | rfl | rfl <;> simp [availOf,function,scalarSelectFunction,defsBefore,defsFrom]
      · intro x member
        have members : x ∈ [100] := by
          rcases p with ⟨cty,ty,hc,ht,ci,ti⟩
          cases cty <;> cases ty <;> simp [Clif.Ty.width] at hc ht ci ti <;> exact member
        have equal : x = 100 := List.mem_singleton.mp members
        subst x
        simp [availOf,function,scalarSelectFunction,defsBefore,defsFrom]
    | succ bi => simp [function,scalarSelectFunction] at found
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function p) (ctx := ctx) (gn := id)).cand tl x available
    have length : (function p).blocks.length = 1 := rfl
    omega
private theorem frame_available (p : Case) (word : BitVec p.cty.width) (ctx : Ctx) :
    (restrict (frame p word) (availOf (function p) (availIn (function p) ctx) 0 0)).regs = (frame p word).regs := by
  funext x
  by_cases present : x = 7 ∨ x = 31 ∨ x = 63
  · rcases present with rfl | rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,scalarSelectFunction,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2.1,present.2.2]
private theorem restrictedDFG (p : Case) (word : BitVec p.cty.width) (input : Inputs p word) :
    DFGCons input.event.ctx (restrict (frame p word) (availOf (function p) (availIn (function p) input.result.ctx) 0 0)) :=
  dfgCons_congr (ctx := input.event.ctx) (fr := frame p word) rfl rfl (frame_available p word input.result.ctx) input.dfg
/-- All16 condition/result widths and every original parameter word inhabit
complete retained select execution and original source-step transfer. Sparse
source IDs, dirty upper machine bits, final aliases, memory and guarded post-frame
are all part of the actual driver witness. Comparison look-through remains separate. -/
theorem stock_select_parameter_complete_source_witness (p : Case) (word : BitVec p.cty.width) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (step : Step) (d : Nat) (fr' : Clif.Frame),
      Stock.lower (function p) = .ok result ∧ LowerScope (function p) ∧ Dominated (function p) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧ record.output.step = some step ∧
      step.decision = .emitted ∧ step.rules.getLast? = some rule_lower_2267.id ∧
      step.results = [[.vreg d .int]] ∧ record.input.base.nextVreg ≤ d ∧ d < record.output.state.base.nextVreg ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst (frame p word,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ∀ world,Runs (fun _ => True) ispec (record.output.emitted.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) (registers p word) world (fun final _ =>
          VHolds ⟨p.ty,Clif.Sem.select word 7 9⟩ (final d) ∧
          (∀ key,key < record.input.base.nextVreg ∨ record.output.state.base.nextVreg ≤ key → final key = registers p word key) ∧
          ValuesHeld (fun value => Demanded record.input value ∧ value ∈ availOf (function p) (availIn (function p) result.ctx) 0 1)
            event.ctx fr' (fun key => final (aliasNum result.final.alias key))) := by
  obtain ⟨input⟩ := inputs p word
  let value : Clif.Val := ⟨p.ty,Clif.Sem.select word 7 9⟩
  let fr' : Clif.Frame := {frame p word with regs := (frame p word).regs.set 100 value,body := []}
  have rawGetC : (frame p word).getAs 7 p.cty = .ok word := by exact getter rfl
  have rawGetX : (frame p word).getAs 31 p.ty = .ok 7 := by exact getter rfl
  have rawGetY : (frame p word).getAs 63 p.ty = .ok 9 := by exact getter rfl
  have getC := (getAs_congr (x := 7) (ty := p.cty) (congrFun (frame_available p word input.result.ctx) 7)).trans rawGetC
  have getX := (getAs_congr (x := 31) (ty := p.ty) (congrFun (frame_available p word input.result.ctx) 31)).trans rawGetX
  have getY := (getAs_congr (x := 63) (ty := p.ty) (congrFun (frame_available p word input.result.ctx) 63)).trans rawGetY
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame p word) Clif.Mem.empty (.select p.ty 7 31 63) = .ok ([value],Clif.Mem.empty) := by
    simp [instOutcome,Clif.evalInst,Clif.Frame.get,getAs_ok rawGetC,rawGetX,rawGetY,value]
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame p word,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.select p.ty 7 31 63,[value],(frame p word).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    · rw [input.results]; rfl
    · rw [input.results]; rfl
  have guarded : ValuesHeld (fun v => Demanded input.record.output.state v ∧ v ∈ availOf (function p) (availIn (function p) input.result.ctx) 0 0)
      input.event.ctx (frame p word) (fun key => registers p word (aliasNum input.result.final.alias key)) :=
    input.held.mono (fun _ needed => needed.1)
  have current : input.record.inst = blockStart (function p) 0 + 0 := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  obtain ⟨d,output,lower,upper,memory,execution⟩ := stock_lower_select_parameter_source_values_derived_types input.run (scope p) (dominated p)
    input.events input.records (bi := 0) (j := 0) (block := (function p).blocks[0]!) rfl rfl current input.source input.clif
    input.parameter input.results rfl input.mapped input.recorded input.emitted
    self (restrictedDFG p word input) getC getX getY guarded sourceStep
  exact ⟨input.result,input.event,input.record,input.step,d,fr',input.run,scope p,dominated p,input.events,input.records,
    input.recorded,input.emitted,input.selectedId,output,lower,upper,sourceStep,execution⟩

/-- Complete actual drivers inhabit both source-DFG preservation and the select
scan adapter, for every condition word and all sixteen scalar width pairs.
The memory relation retains the actual empty source memory. -/
theorem stock_select_complete_scan_witness (p : Case) (word : BitVec p.cty.width) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (fr' : Clif.Frame),
      Stock.lower (function p) = .ok result ∧ LowerScope (function p) ∧ Dominated (function p) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      IndexedSourceInst Clif.Env.empty {funcs := []} (function p) event.ctx 0 record.inst
        (0,frame p word,Clif.Mem.empty) (1,fr',Clif.Mem.empty) ∧
      DFGCons event.ctx (restrict (frame p word) (availOf (function p) (availIn (function p) result.ctx) 0 0)) ∧
      DFGCons event.ctx (restrict fr' (availOf (function p) (availIn (function p) result.ctx) 0 1)) ∧
      ScanFallRefines (IndexedSourceInst Clif.Env.empty {funcs := []} (function p) event.ctx 0) ispec result.final.alias
        (GuardedScanRel (function p) result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)) record ∧
      ∀ world, GuardedScanRel (function p) result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
          record.output.state (0,frame p word,Clif.Mem.empty) (registers p word) world ∧
        ∃ final world', seqRun ispec (record.output.emitted.toList.map
          (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
          (registers p word) world = some (.fall final world') ∧
          GuardedScanRel (function p) result event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
            record.input (1,fr',Clif.Mem.empty) final world' := by
  obtain ⟨input⟩ := inputs p word
  let value : Clif.Val := ⟨p.ty,Clif.Sem.select word 7 9⟩
  let fr' : Clif.Frame := {frame p word with regs := (frame p word).regs.set 100 value,body := []}
  have rawGetC : (frame p word).getAs 7 p.cty = .ok word := by exact getter rfl
  have rawGetX : (frame p word).getAs 31 p.ty = .ok 7 := by exact getter rfl
  have rawGetY : (frame p word).getAs 63 p.ty = .ok 9 := by exact getter rfl
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (frame p word) Clif.Mem.empty (.select p.ty 7 31 63) = .ok ([value],Clif.Mem.empty) := by
    simp [instOutcome,Clif.evalInst,Clif.Frame.get,getAs_ok rawGetC,rawGetX,rawGetY,value]
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (frame p word,Clif.Mem.empty) (fr',Clif.Mem.empty) := by
    refine ⟨input.info,.select p.ty 7 31 63,[value],(frame p word).regs.set 100 value,[],input.source,input.clif,?_,evaluated,?_,rfl⟩
    · rw [input.results]; rfl
    · rw [input.results]; rfl
  have current : input.record.inst = blockStart (function p) 0 + 0 := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using input.current
  have indexed : IndexedSourceInst Clif.Env.empty {funcs := []} (function p) input.event.ctx 0 input.record.inst
      (0,frame p word,Clif.Mem.empty) (1,fr',Clif.Mem.empty) := ⟨current,rfl,sourceStep⟩
  have preDFG := restrictedDFG p word input
  have postDFG := stock_lower_source_step_dfg input.run (scope p) (dominated p) input.events
    (bi := 0) (j := 0) (b := (function p).blocks[0]!) rfl rfl current rfl preDFG sourceStep
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = Clif.Mem.empty) := by
    intro _ _ _ _ _ h; exact h
  have refines := stock_lower_select_scan_fall_refines input.run (scope p) (dominated p) input.events input.records
    (bi := 0) (j := 0) (b := (function p).blocks[0]!) rfl rfl current input.source input.clif
    input.results rfl input.mapped input.recorded input.emitted self stable
    (env := Clif.Env.empty) (cp := {funcs := []})
  refine ⟨input.result,input.event,input.record,fr',input.run,scope p,dominated p,input.events,input.records,
    indexed,preDFG,postDFG,refines,?_⟩
  intro world
  have pre : GuardedScanRel (function p) input.result input.event.ctx 0 (fun _ cm _ => cm = Clif.Mem.empty)
      input.record.output.state (0,frame p word,Clif.Mem.empty) (registers p word) world :=
    ⟨rfl,preDFG,rfl,input.held.mono (fun _ needed => needed.1)⟩
  exact ⟨pre, refines _ _ indexed _ _ pre⟩
end Backend.Stock.Proof.ScalarSelect.ParameterSourceWitness
