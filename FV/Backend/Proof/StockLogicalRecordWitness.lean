module

public import FV.Backend.Proof.StockLogicalRecordValues

@[expose] public section

namespace Backend.Stock.Proof.LogicalSelected
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.LogicalSemantics
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private def formIndex : LogicalForm → Nat
  | .registers => 0 | .immediateRight | .immediateLeft => 1 | .shiftRight | .shiftLeft => 2
private def formAvailable : LogicalForm → List Nat
  | .registers | .immediateRight | .immediateLeft => [7,31]
  | .shiftRight | .shiftLeft => [7,32,31,63]
private def formResultReg : LogicalForm → Nat
  | .registers | .immediateRight | .immediateLeft => 194 | .shiftRight | .shiftLeft => 196
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
private theorem observed (form : LogicalForm) :
    (Stock.lower (formFunction form)).toOption.map (fun result =>
      decide (aliasNum result.final.alias 192 = 192) && decide (aliasNum result.final.alias 193 = 193) &&
      result.blockScans.toList.any (fun event =>
        decide (ctxKey event.ctx = ctxKey (formBuilt form).1) &&
        event.output.records.any (fun record =>
          record.inst == formIndex form &&
          decide (record.output.state.demand = (formDemand form).modify 100 (· + 1)) &&
          record.output.step.any (fun step => step.decision == .emitted &&
            decide (step.rules.getLast? = some Kind.bor.rule.id))))) = some true := by
  cases form <;> decide +kernel
end Runs


/-- Shared actual-run premises for helper/root/record/source witnesses. -/
structure LogicalRecordInputs (form : LogicalForm) where
  result : Result
  event : BlockScanEvent
  record : ScanRecord
  info : IInfo
  step : Step
  run : Stock.lower (formFunction form) = .ok result
  events : event ∈ result.blockScans.toList
  records : record ∈ event.output.records
  current : record.inst = formIndex form
  source : event.ctx.insts[record.inst]? = some info
  clif : info.clif = some (.binary Kind.bor.cop .i64 (formX form) (formY form))
  results : info.results = [100]
  mapped : event.ctx.valueReg? 100 = some (.vreg (formResultReg form) .int)
  recorded : record.output.step = some step
  emitted : step.decision = .emitted
  selectedId : step.rules.getLast? = some Kind.bor.rule.id
  dfg : DFGCons event.ctx (formFrame form)
  held : ValuesHeld (Demanded record.output.state) event.ctx (formFrame form)
    (fun k => formRegs form (aliasNum result.final.alias k))

/-- Actual complete runs supply inhabited premises for every logical selection;
fused definitions are deliberately unmaterialized in the machine file. -/
theorem stock_lower_logical_record_inputs_witness (form : LogicalForm) : Nonempty (LogicalRecordInputs form) := by
  have actual := observed form
  cases run : Stock.lower (formFunction form) with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok result =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,
      decide_eq_true_eq,List.any_eq_true,beq_iff_eq,and_assoc] at actual
    obtain ⟨alias192,alias193,event,events,ctxEq,record,records,current,demand,stepData⟩ := actual
    simp only [ctxKey,Prod.mk.injEq] at ctxEq
    obtain ⟨insts,types,defs,regs⟩ := ctxEq
    obtain ⟨step,recorded,emitted,selectedId⟩ := (by
      simpa only [Option.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] using stepData :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted ∧
          step.rules.getLast? = some Kind.bor.rule.id)
    have keyAt : (event.ctx.insts[record.inst]?).map sourceKey =
        some (some (.binary Kind.bor.cop .i64 (formX form) (formY form)),[100]) := by
      rw [← Array.getElem?_map,insts,current]
      cases form <;> decide +kernel
    obtain ⟨info,source,keyEq⟩ := Option.map_eq_some_iff.mp keyAt
    have clif := congrArg Prod.fst keyEq
    have results := congrArg Prod.snd keyEq
    change info.clif = some (.binary Kind.bor.cop .i64 (formX form) (formY form)) at clif
    change info.results = [100] at results
    have mapped : event.ctx.valueReg? 100 = some (.vreg (formResultReg form) .int) := by
      simp only [Ctx.valueReg?,regs]; cases form <;> rfl
    have dfg : DFGCons event.ctx (formFrame form) := by
      exact dfg_transport insts types defs (formDFG form)
    have held : ValuesHeld (Demanded record.output.state) event.ctx (formFrame form)
        (fun n => formRegs form (aliasNum result.final.alias n)) := by
      intro x needed val lookup
      by_cases seven : x = 7
      · subst x
        change some (.ofInt .i64 7) = some val at lookup
        cases lookup
        refine ⟨192,?_,?_⟩
        · simp only [Ctx.valueReg?,regs]; cases form <;> rfl
        · dsimp only; rw [alias192]; cases form <;> unfold VHolds <;> decide +kernel
      · by_cases thirtyone : x = 31
        · subst x
          cases form with
          | registers =>
            change some (.ofInt .i64 5) = some val at lookup
            cases lookup
            exact ⟨193,by simp only [Ctx.valueReg?,regs]; rfl,by dsimp only; rw [alias193]; unfold VHolds; decide +kernel⟩
          | immediateRight | immediateLeft | shiftRight | shiftLeft =>
            all_goals
              rw [Demanded,demand] at needed
              change 0 ≠ 0 at needed
              exact False.elim (needed rfl)
        · by_cases thirtytwo : x = 32
          · subst x
            cases form with
            | registers | immediateRight | immediateLeft => cases lookup
            | shiftRight | shiftLeft =>
              all_goals
                change some (.ofInt .i64 5) = some val at lookup
                cases lookup
                exact ⟨193,by simp only [Ctx.valueReg?,regs]; rfl,by dsimp only; rw [alias193]; unfold VHolds; decide +kernel⟩
          · by_cases sixtythree : x = 63
            · subst x
              cases form with
              | registers | immediateRight | immediateLeft => cases lookup
              | shiftRight | shiftLeft =>
                all_goals
                  rw [Demanded,demand] at needed
                  change 0 ≠ 0 at needed
                  exact False.elim (needed rfl)
            · cases form <;> simp [formFrame,seven,thirtyone,thirtytwo,sixtythree] at lookup
    exact ⟨⟨result,event,record,info,step,run,events,records,current,source,clif,results,mapped,
      recorded,emitted,selectedId,dfg,held⟩⟩

/-- All five actual selected records establish the original binary value and
preserve every register except the fresh destination through final aliases. -/
theorem stock_lower_logical_record_values_witness (form : LogicalForm) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV),
      Stock.lower (formFunction form) = .ok result ∧ LowerScope (formFunction form) ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) (formRegs form) ρ' ∧
      VHolds ⟨Clif.Ty.i64,Clif.Sem.binary .bor (BitVec.ofNat 64 (formValueX form))
        (BitVec.ofNat 64 (formValueY form))⟩ (ρ' record.input.base.nextVreg) ∧
      ∀ n, n ≠ record.input.base.nextVreg → ρ' n = formRegs form n := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness form
  have sourceX : (formFrame form).getAs (formX form) .i64 = .ok (BitVec.ofNat 64 (formValueX form)) := by
    cases form <;> rfl
  have sourceY : (formFrame form).getAs (formY form) .i64 = .ok (BitVec.ofNat 64 (formValueY form)) := by
    cases form <;> rfl
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  obtain ⟨mi,ρ',outputs,code,upper,execution,value,kept⟩ := stock_lower_logical_record_values
    input.run (formScope form) input.events input.records .bor input.source input.clif input.results
    input.mapped input.recorded input.emitted input.selectedId self input.dfg input.held sourceX sourceY
  exact ⟨input.result,input.event,input.record,ρ',input.run,formScope form,input.events,input.records,execution,value,kept⟩

end Backend.Stock.Proof.LogicalSelected
