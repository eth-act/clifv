import FV.Backend.Proof.StockSourceDefined
import FV.Backend.Proof.StockActualBodyRefines
import FV.Backend.Proof.StockBodyScanRefines
import FV.Backend.Proof.StockMinMaxRegisterDriverRuns
import FV.Backend.Proof.LowerValueRelations

namespace Backend.Stock.Proof.MixedBodyWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open ScalarSelect
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
private def load : Clif.Inst := .load .load .i8 {trapCode := none} 1 0
private def function : Clif.Function := {
  name := "stock_mixed_load_select_body"
  sig := {params := List.replicate 4 ⟨.i64,.none,.normal⟩,returns := [⟨.i64,.none,.normal⟩],callConv := some .systemV}
  blocks := [{id := 0,params := [(1,.i64),(7,.i64),(31,.i64),(63,.i64)],body := [⟨[0],load⟩,⟨[100],.select .i64 7 31 63⟩],term := .ret [100]}] }
private def built := (Stock.buildCtx function).toOption.getD (sinkCtx,#[],sinkState)
private def frame (word : BitVec 64) : Clif.Frame := {
  func := function,slots := [],body := [⟨[0],load⟩,⟨[100],.select .i64 7 31 63⟩],term := .ret [100]
  regs := fun x => if x = 1 then some ⟨.i64,100⟩ else if x = 7 then some ⟨.i64,word⟩
    else if x = 31 then some ⟨.i64,7⟩ else if x = 63 then some ⟨.i64,9⟩ else none }
private def memory : Clif.Mem := {allocs := [⟨100,1,false⟩],bytes := fun x => if x = 100 then some 9 else none}
private def loaded (word : BitVec 64) : Clif.Frame :=
  {frame word with regs := (frame word).regs.set 0 ⟨.i8,9⟩,body := [⟨[100],.select .i64 7 31 63⟩]}
private def selected (word : BitVec 64) : Clif.Frame :=
  {loaded word with regs := (loaded word).regs.set 100 ⟨.i64,Clif.Sem.select word 7 9⟩,body := []}
private def registers (word : BitVec 64) (key : Nat) : CV :=
  BitVec.ofNat 128 (2^100 + if key = 192 then 100 else if key = 193 then word.toNat else if key = 194 then 7 else if key = 195 then 9 else 55)
private def Observed : Prop :=
  (Stock.lower function).toOption.map (fun result =>
    decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
    decide (aliasNum result.final.alias 194 = 194) && decide (aliasNum result.final.alias 195 = 195) && decide (aliasNum result.final.alias 196 = 196) &&
    result.blockScans.toList.any (fun event => decide (minmaxCtxKey event.ctx = minmaxCtxKey built.1) &&
      event.output.records.any (fun sel => sel.inst == 1 && sel.output.step.any (fun step => step.decision == .emitted) &&
        event.output.records.any (fun dead => dead.inst == 0 && decide (dead.input = sel.output.state) &&
          dead.output.step.any (fun step => step.decision == .omitted))))) = some true
section Kernel
attribute [local semireducible] Isle.Aarch64.program Stock.runTerm
private theorem observed : Observed := by unfold Observed; decide +kernel
end Kernel
private theorem scope : LowerScope function := lowerScope_of (by decide +kernel)
private theorem dominated : Dominated function := by
  constructor
  · change ([1,7,31,63,0,100] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    cases bi with
    | zero =>
      simp [function] at found
      subst b
      constructor
      · intro j stm statement x member
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero,Option.some.injEq] at statement
          subst stm
          change x ∈ [1] at member
          have equal := List.mem_singleton.mp member
          subst x
          simp [availOf,function,defsBefore,defsFrom]
        | succ j =>
          cases j <;> simp at statement
          subst stm
          change x ∈ [7,31,63] at member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl | rfl <;> simp [availOf,function,defsBefore,defsFrom]
      · intro x member
        change x ∈ [100] at member
        have equal := List.mem_singleton.mp member
        subst x
        simp [availOf,function,defsBefore,defsFrom]
    | succ bi => simp [function] at found
  · intro ctx ranges st build tl x available notLocal y member
    have bound := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have length : function.blocks.length = 1 := rfl
    omega
private theorem dirty (word : BitVec 64) : (BitVec.ofNat 128 (2^100+word.toNat)).setWidth 64 = word := by
  rw [BitVec.setWidth_ofNat_of_le (by decide : 64 ≤ 128)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,Nat.add_mod,show 2^100 % 2^64 = 0 by decide +kernel,Nat.zero_add,Nat.mod_eq_of_lt word.isLt]
private theorem frame_available (word : BitVec 64) (ctx : Ctx) :
    (restrict (frame word) (availOf function (availIn function ctx) 0 0)).regs = (frame word).regs := by
  funext x
  by_cases present : x = 1 ∨ x = 7 ∨ x = 31 ∨ x = 63
  · rcases present with rfl | rfl | rfl | rfl
    all_goals apply restrict_regs_of_mem; simp [availOf,function,defsBefore,defsFrom]
  · simp only [not_or] at present
    simp [restrict,frame,present.1,present.2.1,present.2.2.1,present.2.2.2]
private theorem source_load : instOutcome Clif.Env.empty {funcs := []} (frame word) memory load =
    .ok ([⟨.i8,9⟩],memory) := by rfl
private theorem source_select : instOutcome Clif.Env.empty {funcs := []} (loaded word) memory (.select .i64 7 31 63) =
    .ok ([⟨.i64,Clif.Sem.select word 7 9⟩],memory) := by rfl
private structure Inputs where
  result : Result
  event : BlockScanEvent
  sel : ScanRecord
  dead : ScanRecord
  selStep : Step
  omitStep : Step
  run : Stock.lower function = .ok result
  events : event ∈ result.blockScans.toList
  sels : sel ∈ event.output.records
  omits : dead ∈ event.output.records
  selCurrent : sel.inst = 1
  omitCurrent : dead.inst = 0
  chain : dead.input = sel.output.state
  selRecorded : sel.output.step = some selStep
  selEmitted : selStep.decision = .emitted
  omitRecorded : dead.output.step = some omitStep
  omitOmitted : omitStep.decision = .omitted
  insts : event.ctx.insts.map minmaxSourceKey = built.1.insts.map minmaxSourceKey
  types : event.ctx.valTy = built.1.valTy
  defs : event.ctx.valDef = built.1.valDef
  maps : event.ctx.valReg = built.1.valReg
  aliasP : aliasNum result.final.alias 192 = 192
  aliasC : aliasNum result.final.alias 193 = 193
  aliasX : aliasNum result.final.alias 194 = 194
  aliasY : aliasNum result.final.alias 195 = 195
  aliasL : aliasNum result.final.alias 196 = 196
private theorem inputs : Nonempty Inputs := by
  have actual := observed
  unfold Observed at actual
  cases run : Stock.lower function with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq,
      List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨aliasP,aliasC,aliasX,aliasY,aliasL,event,events,ctxEq,sel,sels,selCurrent,selStepData,dead,omits,omitCurrent,chain,omitStepData⟩ := actual
    obtain ⟨selStep,selRecorded,selEmitted⟩ := (by simpa only [Option.any_eq_true,beq_iff_eq] using selStepData :
      ∃ step,sel.output.step = some step ∧ step.decision = .emitted)
    obtain ⟨omitStep,omitRecorded,omitOmitted⟩ := (by simpa only [Option.any_eq_true,beq_iff_eq] using omitStepData :
      ∃ step,dead.output.step = some step ∧ step.decision = .omitted)
    simp only [minmaxCtxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,maps⟩ := ctxEq
    exact ⟨⟨result,event,sel,dead,selStep,omitStep,run,events,sels,omits,selCurrent,omitCurrent,chain,
      selRecorded,selEmitted,omitRecorded,omitOmitted,insts,types,defs,maps,aliasP,aliasC,aliasX,aliasY,aliasL⟩⟩
private theorem initialDFG (input : Inputs) (word : BitVec 64) : DFGCons input.event.ctx (frame word) := by
  constructor
  · intro x j info cl v defined found original pure lookup
    by_cases hp : x = 1
    · subst x; change (input.event.ctx.valDef[1]?).join = some j at defined
      rw [input.defs] at defined; cases defined
    · by_cases hc : x = 7
      · subst x; change (input.event.ctx.valDef[7]?).join = some j at defined
        rw [input.defs] at defined; cases defined
      · by_cases hx : x = 31
        · subst x; change (input.event.ctx.valDef[31]?).join = some j at defined
          rw [input.defs] at defined; cases defined
        · by_cases hy : x = 63
          · subst x; change (input.event.ctx.valDef[63]?).join = some j at defined
            rw [input.defs] at defined; cases defined
          · simp [frame,hp,hc,hx,hy] at lookup
  · intro x t v type lookup
    by_cases hp : x = 1
    · subst x; have typed : input.event.ctx.valueType? 1 = some (.int 64) := by change (input.event.ctx.valTy[1]?).join = _; rw [input.types]; rfl
      rw [typed] at type; cases type
      simp only [frame,ite_true,Option.some.injEq] at lookup; subst v; rfl
    · by_cases hc : x = 7
      · subst x; have typed : input.event.ctx.valueType? 7 = some (.int 64) := by change (input.event.ctx.valTy[7]?).join = _; rw [input.types]; rfl
        rw [typed] at type; cases type
        simp only [frame,hp,ite_false,ite_true,Option.some.injEq] at lookup; subst v; rfl
      · by_cases hx : x = 31
        · subst x; have typed : input.event.ctx.valueType? 31 = some (.int 64) := by change (input.event.ctx.valTy[31]?).join = _; rw [input.types]; rfl
          rw [typed] at type; cases type
          simp only [frame,hp,hc,ite_false,ite_true,Option.some.injEq] at lookup; subst v; rfl
        · by_cases hy : x = 63
          · subst x; have typed : input.event.ctx.valueType? 63 = some (.int 64) := by change (input.event.ctx.valTy[63]?).join = _; rw [input.types]; rfl
            rw [typed] at type; cases type
            simp only [frame,hp,hc,hx,ite_false,ite_true,Option.some.injEq] at lookup; subst v; rfl
          · simp [frame,hp,hc,hx,hy] at lookup
private theorem initialHeld (input : Inputs) (word : BitVec 64) (st : State) :
    ValuesHeld (Demanded st) input.event.ctx (frame word)
      (fun key => registers word (aliasNum input.result.final.alias key)) := by
  intro x needed v lookup
  by_cases hp : x = 1
  · subst x; simp only [frame,ite_true,Option.some.injEq] at lookup; subst v
    refine ⟨192,?_,?_⟩
    · change (input.event.ctx.valReg[1]?).join = _; rw [input.maps]; rfl
    · dsimp only; rw [input.aliasP]; exact dirty 100
  · by_cases hc : x = 7
    · subst x; simp only [frame,hp,ite_false,ite_true,Option.some.injEq] at lookup; subst v
      refine ⟨193,?_,?_⟩
      · change (input.event.ctx.valReg[7]?).join = _; rw [input.maps]; rfl
      · dsimp only; rw [input.aliasC]; exact dirty word
    · by_cases hx : x = 31
      · subst x; simp only [frame,hp,hc,ite_false,ite_true,Option.some.injEq] at lookup; subst v
        refine ⟨194,?_,?_⟩
        · change (input.event.ctx.valReg[31]?).join = _; rw [input.maps]; rfl
        · dsimp only; rw [input.aliasX]; exact dirty 7
      · by_cases hy : x = 63
        · subst x; simp only [frame,hp,hc,hx,ite_false,ite_true,Option.some.injEq] at lookup; subst v
          refine ⟨195,?_,?_⟩
          · change (input.event.ctx.valReg[63]?).join = _; rw [input.maps]; rfl
          · dsimp only; rw [input.aliasY]; exact dirty 9
        · simp [frame,hp,hc,hx,hy] at lookup

private theorem source_at (input : Inputs) (which : Bool) :
    ∃ info,input.event.ctx.insts[if which then 1 else 0]? = some info ∧
      info.clif = some (if which then .select .i64 7 31 63 else load) ∧
      info.results = [if which then 100 else 0] := by
  have key : (input.event.ctx.insts[if which then 1 else 0]?).map minmaxSourceKey =
      some (some (if which then .select .i64 7 31 63 else load),[if which then 100 else 0]) := by
    rw [← Array.getElem?_map,input.insts,Array.getElem?_map]
    cases which <;> rfl
  obtain ⟨info,found,equal⟩ := Option.map_eq_some_iff.mp key
  exact ⟨info,found,congrArg Prod.fst equal,congrArg Prod.snd equal⟩
private theorem scans_execute {exec : Nat → State → Except String Scan}
    {indices : List Nat} {input : State} {output : BlockScan}
    (cert : ScansSpec exec indices input output) :
    ∀ record ∈ output.records, exec record.inst record.input = .ok record.output := by
  induction cert with
  | nil input => simp
  | cons head rest ih =>
    intro record member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih record member
private theorem actual_record (input : Inputs) {record : ScanRecord} (member : record ∈ input.event.output.records) :
    scanInstruction input.event.ctx input.event.block record.inst input.event.termInst input.event.isBranch record.input =
      .ok record.output := by
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, bi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin input.run input.events
  rw [eventEq] at member ⊢
  have actual := (stock_lowerBlockCore_scanOrigin coreRun).2.2.2.2.2
  unfold scanBlock at actual
  exact scans_execute (runScans_spec actual) record member

/-- A complete actual driver combines a nontrapping load whose result is
ignored with an emitted select. For every condition word, both real source steps
and the actual ordinary-body code preserve the indexed guarded relation, DFG,
and actual source memory. The return record is excluded explicitly. -/
theorem stock_mixed_load_select_body_witness (word : BitVec 64) :
    ∃ (result : Result) (event : BlockScanEvent) (sel dead : ScanRecord) (body : BlockScan),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ sel ∈ event.output.records ∧ dead ∈ event.output.records ∧
      sel.inst = 1 ∧ dead.inst = 0 ∧ body.records = [sel,dead] ∧ dead.output.emitted = #[] ∧
      ScansSpec (fun i => scanInstruction event.ctx event.block i event.termInst event.isBranch)
        [1,0] sel.input body ∧
      (∀ r ∈ body.records, SelectOrOmittedRecord function event.ctx 0 r) ∧
      event.ctx.valueReg? 0 = some (.vreg 196 .int) ∧ aliasNum result.final.alias 196 = 196 ∧
      ¬ VHolds ⟨.i8,9⟩ (registers word (aliasNum result.final.alias 196)) ∧
      (loaded word).regs 0 = some ⟨.i8,9⟩ ∧
      Clif.step Clif.Env.empty {funcs := []} ⟨frame word,[],memory⟩ = .next ⟨loaded word,[],memory⟩ ∧
      Clif.step Clif.Env.empty {funcs := []} ⟨loaded word,[],memory⟩ = .next ⟨selected word,[],memory⟩ ∧
      SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx 0) [0,1]
        (0,frame word,memory) (2,selected word,memory) ∧
      ScanFallRefines (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx 0) ispec result.final.alias
        (GuardedScanRel function result event.ctx 0 (fun _ cm _ => cm = memory)) dead ∧
      ∀ world, GuardedScanRel function result event.ctx 0 (fun _ cm _ => cm = memory)
          body.state (0,frame word,memory) (registers word) world ∧
        ∃ final world', seqRun ispec (body.code.toList.map
          (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
          (registers word) world = some (.fall final world') ∧
          GuardedScanRel function result event.ctx 0 (fun _ cm _ => cm = memory)
            sel.input (2,selected word,memory) final world' := by
  obtain ⟨input⟩ := inputs
  obtain ⟨loadInfo,loadFound,loadClif,loadResults⟩ := source_at input false
  obtain ⟨selectInfo,selectFound,selectClif,selectResults⟩ := source_at input true
  have loadSource : input.event.ctx.insts[input.dead.inst]? = some loadInfo := by rw [input.omitCurrent]; exact loadFound
  have selectSource : input.event.ctx.insts[input.sel.inst]? = some selectInfo := by rw [input.selCurrent]; exact selectFound
  have loadStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.dead.inst
      (frame word,memory) (loaded word,memory) := by
    refine ⟨loadInfo,load,[⟨.i8,9⟩],(frame word).regs.set 0 ⟨.i8,9⟩,[⟨[100],.select .i64 7 31 63⟩],
      loadSource,loadClif,?_,source_load,?_,rfl⟩
    · rw [loadResults]; rfl
    · rw [loadResults]; rfl
  have selectStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.sel.inst
      (loaded word,memory) (selected word,memory) := by
    refine ⟨selectInfo,.select .i64 7 31 63,[⟨.i64,Clif.Sem.select word 7 9⟩],
      (loaded word).regs.set 100 ⟨.i64,Clif.Sem.select word 7 9⟩,[],selectSource,selectClif,?_,source_select,?_,rfl⟩
    · rw [selectResults]; rfl
    · rw [selectResults]; rfl
  have indexedLoad : IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx 0 input.dead.inst
      (0,frame word,memory) (1,loaded word,memory) := ⟨input.omitCurrent,rfl,loadStep⟩
  have indexedSelect : IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx 0 input.sel.inst
      (1,loaded word,memory) (2,selected word,memory) := ⟨input.selCurrent,rfl,selectStep⟩
  have sourceSteps : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function input.event.ctx 0) [0,1]
      (0,frame word,memory) (2,selected word,memory) := by
    have h0 := indexedLoad; rw [input.omitCurrent] at h0
    have h1 := indexedSelect; rw [input.selCurrent] at h1
    exact .cons h0 (.cons h1 (.nil _))
  have selRun := actual_record input input.sels
  have deadRun := actual_record input input.omits
  have noCode := (scan_omitted deadRun input.omitRecorded input.omitOmitted).2.2.2.2.2.2.2.1
  let body : BlockScan := ⟨input.dead.output.state,[input.sel,input.dead],input.dead.output.emitted ++ input.sel.output.emitted⟩
  have rebuild0 : (⟨0,input.dead.input,input.dead.output⟩ : ScanRecord) = input.dead := by
    rw [← input.omitCurrent]
  have rebuild1 : (⟨1,input.sel.input,input.sel.output⟩ : ScanRecord) = input.sel := by
    rw [← input.selCurrent]
  have tail : ScansSpec (fun i => scanInstruction input.event.ctx input.event.block i input.event.termInst input.event.isBranch)
      [0] input.sel.output.state ⟨input.dead.output.state,[input.dead],input.dead.output.emitted⟩ := by
    rw [← input.chain]
    rw [input.omitCurrent] at deadRun
    simpa only [Array.empty_append,rebuild0] using (ScansSpec.cons (exec := fun i => scanInstruction input.event.ctx input.event.block i input.event.termInst input.event.isBranch) deadRun (ScansSpec.nil input.dead.output.state))
  have scanned : ScansSpec (fun i => scanInstruction input.event.ctx input.event.block i input.event.termInst input.event.isBranch)
      [1,0] input.sel.input body := by
    rw [input.selCurrent] at selRun
    simpa only [rebuild1] using (ScansSpec.cons (exec := fun i => scanInstruction input.event.ctx input.event.block i input.event.termInst input.event.isBranch) selRun tail)
  have retained : ∀ r ∈ body.records, r ∈ input.event.output.records := by
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact input.sels
    · have equal := List.mem_singleton.mp member; subst r; exact input.omits
  have mapped : input.event.ctx.valueReg? 100 = some (.vreg 197 .int) := by
    change (input.event.ctx.valReg[100]?).join = _; rw [input.maps]; rfl
  have families : ∀ r ∈ body.records, SelectOrOmittedRecord function input.event.ctx 0 r := by
    intro r member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨1,function.blocks[0]!,⟨[100],.select .i64 7 31 63⟩,rfl,rfl,input.selCurrent,
        input.selStep,input.selRecorded,.inr ⟨input.selEmitted,selectInfo,.i64,7,31,63,100,197,
          selectSource,selectClif,selectResults,rfl,mapped⟩⟩
    · have equal := List.mem_singleton.mp member; subst r
      exact ⟨0,function.blocks[0]!,⟨[0],load⟩,rfl,rfl,input.omitCurrent,
        input.omitStep,input.omitRecorded,.inl input.omitOmitted⟩
  have omitted := stock_lower_omitted_scan_fall_refines input.run scope dominated input.events input.omits
    (bi := 0) (j := 0) (b := function.blocks[0]!) rfl rfl input.omitCurrent input.omitRecorded input.omitOmitted
    (isem := ispec) (MR := fun _ cm _ => cm = memory) (env := Clif.Env.empty) (cp := {funcs := []})
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = memory) := by intro _ _ _ _ _ h; exact h
  have composed := stock_lower_select_omitted_body_fall_refines input.run scope dominated input.events
    scanned retained families self stable (env := Clif.Env.empty) (cp := {funcs := []})
  have preDFG := dfgCons_congr (ctx := input.event.ctx) (fr := frame word)
    (fr' := restrict (frame word) (availOf function (availIn function input.result.ctx) 0 0))
    rfl rfl (frame_available word input.result.ctx) (initialDFG input word)
  have loadMapped : input.event.ctx.valueReg? 0 = some (.vreg 196 .int) := by
    change (input.event.ctx.valReg[0]?).join = _; rw [input.maps]; rfl
  have ignoredNotHeld : ¬ VHolds ⟨.i8,9⟩ (registers word (aliasNum input.result.final.alias 196)) := by
    rw [input.aliasL]
    change ¬ ((BitVec.ofNat 128 (2^100+55)).setWidth 8 = (9 : BitVec 8))
    decide +kernel
  refine ⟨input.result,input.event,input.sel,input.dead,body,input.run,scope,dominated,input.events,input.sels,input.omits,
    input.selCurrent,input.omitCurrent,rfl,noCode,scanned,families,loadMapped,input.aliasL,ignoredNotHeld,rfl,rfl,rfl,sourceSteps,omitted,?_⟩
  intro world
  have pre : GuardedScanRel function input.result input.event.ctx 0 (fun _ cm _ => cm = memory)
      body.state (0,frame word,memory) (registers word) world :=
    ⟨rfl,preDFG,rfl,(initialHeld input word body.state).mono (fun _ needed => needed.1)⟩
  exact ⟨pre,composed _ _ sourceSteps _ _ pre⟩

private theorem list_pair {α : Type} (xs : List α) (length : xs.length = 2) :
    ∃ a b, xs = [a,b] := by
  cases xs with
  | nil => simp at length
  | cons a rest =>
    cases rest with
    | nil => simp at length
    | cons b rest =>
      cases rest with
      | nil => exact ⟨a,b,rfl⟩
      | cons c rest => simp at length

/-- The mixed complete driver also inhabits the general whole-driver-derived
body split and semantic connection. Body certificates and source positions come
from the real driver, including separation of its actual return record. -/
theorem stock_mixed_actual_body_split_witness (word : BitVec 64) :
    ∃ (result : Result) (event : BlockScanEvent) (b : Clif.Block) (term : ScanRecord) (body : BlockScan),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧
      event ∈ result.blockScans.toList ∧ SourceBodySplit function event b term body ∧
      event.block = 0 ∧ b.body.length = 2 ∧ term.inst = 2 ∧ body.records.map (·.inst) = [1,0] ∧
      (∀ r ∈ body.records, SelectOrOmittedRecord function event.ctx event.block r) ∧
      SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx event.block)
        ((List.range b.body.length).map (blockStart function event.block + ·))
        (0,frame word,memory) (2,selected word,memory) ∧
      ∀ world, GuardedScanRel function result event.ctx event.block (fun _ cm _ => cm = memory)
          event.output.state (0,frame word,memory) (registers word) world ∧
        ∃ final world',seqRun ispec (body.code.toList.map
          (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))))
          (registers word) world = some (.fall final world') ∧
          GuardedScanRel function result event.ctx event.block (fun _ cm _ => cm = memory)
            term.output.state (2,selected word,memory) final world' := by
  obtain ⟨result,event,sel,dead,oldBody,run,scope,dominated,events,sels,deads,selInst,deadInst,
    oldRecords,noCode,oldScan,oldFamilies,loadMap,loadAlias,notHeld,loadedValue,loadStep,selectStep,sourceSteps,omitted,executions⟩ :=
    stock_mixed_load_select_body_witness word
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ world _ h => ⟨world,h,SameWorld.refl _ _⟩
  have stable : MRStable (fun _ => True) (fun _ cm _ => cm = memory) := by intro _ _ _ _ _ h; exact h
  obtain ⟨b,term,body,split,semantic⟩ := stock_lower_actual_select_omitted_body_refines run scope dominated events self stable
    (env := Clif.Env.empty) (cp := {funcs := []})
  have blockIndex : event.block = 0 := by
    have bound := (List.getElem?_eq_some_iff.mp split.block).1
    have length : function.blocks.length = 1 := rfl
    omega
  have blockEq : b = function.blocks[0]! := by
    have found := split.block
    rw [blockIndex] at found
    exact Option.some.inj found.symm
  have termIndex : term.inst = 2 := by
    rw [split.termInst,split.termIndex,blockIndex,blockEq]
    rfl
  have order : body.records.map (·.inst) = [1,0] := by
    rw [split.scanned.order,sourceBodyIndices,blockIndex,blockEq]
    rfl
  have length : body.records.length = 2 := by
    have same := congrArg List.length order
    simpa only [List.length_map,List.length_cons,List.length_nil] using same
  obtain ⟨first,last,pair⟩ := list_pair body.records length
  have pairOrder := order
  rw [pair] at pairOrder
  simp only [List.map_cons,List.map_nil,List.cons.injEq] at pairOrder
  have firstIndex : first.inst = 1 := pairOrder.1
  have lastIndex : last.inst = 0 := pairOrder.2.1
  have selFirst : sel = first := by
    rw [split.records,pair] at sels
    simp only [List.mem_cons,List.not_mem_nil,or_false] at sels
    rcases sels with equal | equal | equal
    · have h := congrArg ScanRecord.inst equal; omega
    · exact equal
    · have h := congrArg ScanRecord.inst equal; omega
  have deadLast : dead = last := by
    rw [split.records,pair] at deads
    simp only [List.mem_cons,List.not_mem_nil,or_false] at deads
    rcases deads with equal | equal | equal
    · have h := congrArg ScanRecord.inst equal; omega
    · have h := congrArg ScanRecord.inst equal; omega
    · exact equal
  have records : body.records = [sel,dead] := by rw [pair,selFirst,deadLast]
  have families : ∀ r ∈ body.records, SelectOrOmittedRecord function event.ctx event.block r := by
    intro r member
    rw [blockIndex]
    apply oldFamilies r
    rwa [oldRecords,← records]
  have oldState : oldBody.state = dead.output.state := by
    have chain := oldScan.chain
    rw [oldRecords] at chain
    exact chain.2.2
  have bodyState : body.state = dead.output.state := by
    have chain := split.scanned.chain
    rw [records] at chain
    exact chain.2.2
  have indexed : SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx event.block)
      ((List.range b.body.length).map (blockStart function event.block + ·))
      (0,frame word,memory) (2,selected word,memory) := by
    rw [blockIndex,blockEq]
    exact sourceSteps
  refine ⟨result,event,b,term,body,run,scope,dominated,events,split,blockIndex,?_,termIndex,order,families,indexed,?_⟩
  · rw [blockEq]; rfl
  · intro world
    have pre := (executions world).1
    have actualPre : GuardedScanRel function result event.ctx event.block (fun _ cm _ => cm = memory)
        event.output.state (0,frame word,memory) (registers word) world := by
      rw [blockIndex,← split.state,bodyState,← oldState]
      exact pre
    exact ⟨actualPre,semantic families _ _ indexed _ _ actualPre⟩

/-- Actual source definedness survives both the ignored load and emitted select
of the complete mixed driver, including both newly bound source results. -/
theorem stock_mixed_source_defined_witness (word : BitVec 64) :
    ∃ (result : Result) (event : BlockScanEvent), Stock.lower function = .ok result ∧
      LowerScope function ∧ Dominated function ∧ event ∈ result.blockScans.toList ∧
      SourceDefinedAt function result.ctx 0 0 (frame word) ∧
      SourceSteps (IndexedSourceInst Clif.Env.empty {funcs := []} function event.ctx 0) [0,1]
        (0,frame word,memory) (2,selected word,memory) ∧
      SourceDefinedAt function result.ctx 0 2 (selected word) := by
  obtain ⟨result,event,sel,dead,oldBody,run,scope,dominated,events,sels,deads,selInst,deadInst,
    oldRecords,noCode,oldScan,oldFamilies,loadMap,loadAlias,notHeld,loadedValue,loadStep,selectStep,sourceSteps,omitted,executions⟩ :=
    stock_mixed_load_select_body_witness word
  have initial : SourceDefinedAt function result.ctx 0 0 (frame word) := by
    intro x available
    obtain ⟨present,_⟩ := (mem_av (f := function) (bi := 0) (B := function.blocks[0]!) (by rfl)).mp available
    rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
    · change x ∈ [1,7,31,63] at parameter
      simp only [List.mem_cons,List.not_mem_nil,or_false] at parameter
      rcases parameter with rfl | rfl | rfl | rfl <;> simp [frame]
    · have bound := (inFix_fixOk (f := function) (ctx := result.ctx) (gn := id)).cand 0 x incoming
      omega
    · omega
  have final : SourceDefinedAt function result.ctx 0 2 (selected word) := by
    cases sourceSteps with
    | cons first tail =>
      cases tail with
      | cons second tail =>
        cases tail
        have one := stock_lower_source_defined_step run scope dominated events
          (bi := 0) (j := 0) (i := 0) (b := function.blocks[0]!) rfl rfl rfl initial first.2.2
        exact stock_lower_source_defined_step run scope dominated events
          (bi := 0) (j := 1) (i := 1) (b := function.blocks[0]!) rfl rfl rfl one second.2.2
  exact ⟨result,event,run,scope,dominated,events,initial,sourceSteps,final⟩
end Backend.Stock.Proof.MixedBodyWitness
