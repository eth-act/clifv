import FV.Backend.Proof.StockMemoryStoreSelection
import FV.Backend.Proof.LowerDecide

namespace Backend.Stock.Memory.StoreRoots
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000

private def flags : Clif.MemFlags := {trapCode := none}
private def fixture (kind : Kind) : Clif.Function := {
  name := "stock_integer_store"
  sig := {
    params := [⟨.i64,.none,.normal⟩,⟨kind.sourceTy,.none,.normal⟩]
    returns := []
    callConv := some .systemV }
  blocks := [{
    id := 0
    params := [(0,.i64),(1,kind.sourceTy)]
    body := [⟨[],.store kind.sourceOp kind.sourceTy flags 1 0 0⟩]
    term := .ret [] }] }

private def built (kind : Kind) : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx (fixture kind)).toOption.getD (sinkCtx,#[],sinkState)
private theorem build_ok (kind : Kind) : Stock.buildCtx (fixture kind) = .ok (built kind) := by
  cases kind <;> rfl
private theorem pointer_parameter (kind : Kind) : (built kind).1.defInst? 0 = none := by
  cases kind <;> rfl
private theorem value_parameter (kind : Kind) : (built kind).1.defInst? 1 = none := by
  cases kind <;> rfl
private theorem pointer_mapped (kind : Kind) : (built kind).1.valueReg? 0 = some (.vreg 192 .int) := by
  cases kind <;> rfl
private theorem value_mapped (kind : Kind) : (built kind).1.valueReg? 1 = some (.vreg 193 .int) := by
  cases kind <;> rfl

private def rootWitnessOk (kind : Kind) : Bool :=
  match Stock.runTerm (built kind).1 "lower" [.inst 0] (built kind).2.2 with
  | .ok (some _,_,trace) => decide (trace.getLast? = some kind.root.id)
  | _ => false
private theorem roots_succeed (kind : Kind) : rootWitnessOk kind = true := by
  cases kind <;> decide +kernel

/-- Each of the seven actual store roots wins first-match selection in a source-built context. -/
theorem integer_store_root_witness (kind : Kind) :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat))
      (st next : State) (out : V) (trace : List RuleId),
      Stock.buildCtx f = .ok (ctx,ranges,st) ∧
      ctx.valueReg? 0 = some (.vreg 192 .int) ∧
      ctx.valueReg? 1 = some (.vreg 193 .int) ∧
      Stock.runTerm ctx "lower" [.inst 0] st = .ok (some out,next,trace) ∧
      trace.getLast? = some kind.root.id := by
  have checked := roots_succeed kind
  unfold rootWitnessOk at checked
  cases actual : Stock.runTerm (built kind).1 "lower" [.inst 0] (built kind).2.2 with
  | error error => rw [actual] at checked; cases checked
  | ok result =>
    obtain ⟨out,next,trace⟩ := result
    rw [actual] at checked
    cases out with
    | none => cases checked
    | some out =>
      exact ⟨fixture kind,(built kind).1,(built kind).2.1,(built kind).2.2,
        next,out,trace,build_ok kind,pointer_mapped kind,value_mapped kind,
        actual,of_decide_eq_true checked⟩

/-- Every store RHS has a complete source-built demand, payload and emitted-instruction witness. -/
theorem integer_store_rhs_witness (kind : Kind) :
    ∃ (ctx : Ctx) (st : State) (trace : Array RuleId),
      ctx.valueReg? 0 = some (.vreg 192 .int) ∧ ctx.valueReg? 1 = some (.vreg 193 .int) ∧
      (evalExpr program (Stock.sem ctx) {} 140 kind.root.rhs
        (env4 (.value 1) (.value 0) (.op (.memFlags flags)) (.int 0))).run (st,#[]) =
      .ok (some (.regsVec []),
        {(st.mark 0).mark 1 with base := st.base.emit (.store kind.storeOp (.vreg 193 .int) (.unsignedOffset (.vreg 192 .int) 0) flags)},trace) := by
  have safe : DemandAllowed (built kind).1 (built kind).2.2 1 := by
    intro i defined
    rw [value_parameter kind] at defined
    cases defined
  obtain ⟨trace,run⟩ := stock_parameter_integer_store_rhs data_program kind (built kind).1
    (cfg := {}) rfl (pointer_parameter kind) (pointer_mapped kind) (value_mapped kind)
    flags (built kind).2.2 #[] 0 safe
  exact ⟨(built kind).1,(built kind).2.2,trace,pointer_mapped kind,value_mapped kind,run⟩

private def loweringWitnessOk (kind : Kind) : Option Bool :=
  (Stock.lower (fixture kind)).toOption.map fun result =>
    result.blockScans.toList.any fun event => event.output.records.any fun record =>
      record.inst == 0 && decide (record.output.emitted =
        #[.store kind.storeOp (.vreg 193 .int) (.unsignedOffset (.vreg 192 .int) 0) flags]) &&
      record.output.step.any (fun step => step.decision == .emitted)
private theorem lowering_succeeds (kind : Kind) : loweringWitnessOk kind = some true := by
  cases kind <;> decide +kernel

/-- Complete lowering retains an emitted store for all seven roots, with nonidentity operand registers. -/
theorem integer_store_lowering_witness (kind : Kind) :
    ∃ (f : Clif.Function) (result : Result) (event : BlockScanEvent) (record : ScanRecord),
      Stock.lower f = .ok result ∧ event ∈ result.blockScans.toList ∧
      record ∈ event.output.records ∧ record.inst = 0 ∧
      record.output.emitted =
        #[.store kind.storeOp (.vreg 193 .int) (.unsignedOffset (.vreg 192 .int) 0) flags] ∧
      ∃ step,record.output.step = some step ∧ step.decision = .emitted := by
  have observed := lowering_succeeds kind
  unfold loweringWitnessOk at observed
  cases run : Stock.lower (fixture kind) with
  | error error => simp only [run,Except.toOption,Option.map_none] at observed; cases observed
  | ok result =>
    simp only [run,Except.toOption,Option.map_some,Option.some.injEq] at observed
    obtain ⟨event,events,record,records,current,code,step⟩ :=
      (by simpa only [List.any_eq_true,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq,and_assoc] using observed :
        ∃ event ∈ result.blockScans.toList,∃ record ∈ event.output.records,
          record.inst = 0 ∧ record.output.emitted =
            #[.store kind.storeOp (.vreg 193 .int) (.unsignedOffset (.vreg 192 .int) 0) flags] ∧
          record.output.step.any (fun step => step.decision == .emitted) = true)
    obtain ⟨step,recorded,emitted⟩ :=
      (by simpa only [Option.any_eq_true,beq_iff_eq] using step :
        ∃ step,record.output.step = some step ∧ step.decision = .emitted)
    exact ⟨fixture kind,result,event,record,run,events,records,current,code,step,recorded,emitted⟩

end Backend.Stock.Memory.StoreRoots
