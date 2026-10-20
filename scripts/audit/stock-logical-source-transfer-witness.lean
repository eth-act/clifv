import FV.Backend.Proof.StockLogicalSourceTransfer
import FV.Backend.Proof.StockLogicalNotRecordWitness
import FV.Backend.Proof.StockLogicalSourceWitness

open Lean Elab Command
-- Test-only aliases refer to the existing checked concrete witnesses. The
-- kernel checks each definition; no private name enters the production module.
run_cmd do
  let aliases : List (String × String) := [("oldNotFunction", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.function"),
    ("oldNotInputs", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.inputs"),
    ("oldNotFrame", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.frame"),
    ("oldNotScope", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.scope"),
    ("oldNotDominated", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.dominated"),
    ("oldNotAvailable", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.frame_available"),
    ("oldNotRegs", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.regs"),
    ("oldRrFrame", "_private.FV.Backend.Proof.StockLogicalSourceWitness.0.Backend.Stock.Proof.LogicalSelected.rrFrame"),
    ("oldRrDominated", "_private.FV.Backend.Proof.StockLogicalSourceWitness.0.Backend.Stock.Proof.LogicalSelected.rrDominated"),
    ("oldRrRestricted", "_private.FV.Backend.Proof.StockLogicalSourceWitness.0.Backend.Stock.Proof.LogicalSelected.rrRestricted"),
    ("oldNotInputResult", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.result"),
    ("oldNotInputEvent", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.event"),
    ("oldNotInputRecord", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.record"),
    ("oldNotInputInfo", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.info"),
    ("oldNotInputStep", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.step"),
    ("oldNotInputRun", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.run"),
    ("oldNotInputEvents", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.events"),
    ("oldNotInputRecords", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.records"),
    ("oldNotInputCurrent", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.current"),
    ("oldNotInputSource", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.source"),
    ("oldNotInputClif", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.clif"),
    ("oldNotInputResults", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.results"),
    ("oldNotInputMapped", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.mapped"),
    ("oldNotInputRecorded", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.recorded"),
    ("oldNotInputEmitted", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.emitted"),
    ("oldNotInputSelectedId", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.selectedId"),
    ("oldNotInputDfg", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.dfg"),
    ("oldNotInputHeld", "_private.FV.Backend.Proof.StockLogicalNotRecordWitness.0.Backend.Stock.Proof.LogicalNot.MirrorWitness.Inputs.held")]
  for (newName, oldText) in aliases do
    let env ← getEnv
    let some (oldName,info) := env.constants.toList.find? (fun (name,_) => name.toString == oldText)
      | throwError "missing pinned witness {oldText}"
    liftCoreM <| addDecl <| .defnDecl {
      name := Name.mkSimple newName
      levelParams := info.levelParams
      type := info.type
      value := mkConst oldName (info.levelParams.map Level.param)
      hints := .abbrev
      safety := .safe }

attribute [reducible] oldNotFunction oldNotInputs oldNotFrame oldNotScope oldNotDominated oldNotAvailable oldNotRegs oldRrFrame oldRrDominated oldRrRestricted oldNotInputResult oldNotInputEvent oldNotInputRecord oldNotInputInfo oldNotInputStep oldNotInputRun oldNotInputEvents oldNotInputRecords oldNotInputCurrent oldNotInputSource oldNotInputClif oldNotInputResults oldNotInputMapped oldNotInputRecorded oldNotInputEmitted oldNotInputSelectedId oldNotInputDfg oldNotInputHeld

namespace Backend.Stock.Proof.LogicalSourceTests
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open LogicalSelected LogicalComplete LogicalSemantics
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
theorem mirrored_source_witness (kind : Kind) (left : Bool) (ty : Clif.Ty)
    (supported : ty = .i32 ∨ ty = .i64) :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (oldNotFunction kind left ty) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) oldNotRegs ρ' ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (oldNotFrame kind left ty,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (oldNotFunction kind left ty) (availIn (oldNotFunction kind left ty) result.ctx) 0 ((1 : Nat)+1))
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := oldNotInputs kind left ty supported
  have restrictedDFG := dfgCons_congr (ctx := (oldNotInputEvent input).ctx) (fr := oldNotFrame kind left ty)
    (fr' := restrict (oldNotFrame kind left ty) (availOf (oldNotFunction kind left ty) (availIn (oldNotFunction kind left ty) (oldNotInputResult input).ctx) 0 ((1 : Nat))))
    rfl rfl (oldNotAvailable kind left ty (oldNotInputResult input).ctx) (oldNotInputDfg input)
  have guarded := (oldNotInputHeld input).mono (fun y (h : Demanded (oldNotInputRecord input).output.state y ∧ y ∈
    availOf (oldNotFunction kind left ty) (availIn (oldNotFunction kind left ty) (oldNotInputResult input).ctx) 0 ((1 : Nat))) => h.1)
  have block : (oldNotFunction kind left ty).blocks[0]? = some ((oldNotFunction kind left ty).blocks[0]!) := rfl
  have statement : ((oldNotFunction kind left ty).blocks[0]!).body[(1 : Nat)]? =
      some (⟨[100],.binary kind.cop ty (if left then 63 else 7) (if left then 7 else 63)⟩ : Clif.Stmt) := by rfl
  have current : (oldNotInputRecord input).inst = blockStart (oldNotFunction kind left ty) 0 + (1 : Nat) := by
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using (oldNotInputCurrent input)
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  let val : Clif.Val := ⟨ty,Clif.Sem.binary kind.cop (if left then ~~~(BitVec.ofNat ty.width 5) else BitVec.ofNat ty.width 7) (if left then BitVec.ofNat ty.width 7 else ~~~(BitVec.ofNat ty.width 5))⟩
  let fr' : Clif.Frame := {oldNotFrame kind left ty with regs := (oldNotFrame kind left ty).regs.set 100 val,body := []}
  have evaluated : instOutcome Clif.Env.empty {funcs := []} (oldNotFrame kind left ty) Clif.Mem.empty
      (.binary kind.cop ty (if left then 63 else 7) (if left then 7 else 63)) = .ok ([val],Clif.Mem.empty) := by
    cases kind <;> cases left <;> rcases supported with rfl | rfl <;> rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} (oldNotInputEvent input).ctx (oldNotInputRecord input).inst
      (oldNotFrame kind left ty,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨(oldNotInputInfo input),.binary kind.cop ty (if left then 63 else 7) (if left then 7 else 63),[val],(oldNotFrame kind left ty).regs.set 100 val,[],
      (oldNotInputSource input),(oldNotInputClif input),by rw [(oldNotInputResults input)]; rfl,evaluated,by rw [(oldNotInputResults input)]; rfl,rfl⟩
  obtain ⟨u,v,ρ',getU,getV,execution,value,memory,kept,sourceHeld⟩ :=
    not_source_from_step (oldNotInputRun input) (oldNotScope kind left ty supported)
      (oldNotDominated kind left ty supported) (oldNotInputEvents input) (oldNotInputRecords input) block statement current kind left
      (oldNotInputSource input) (oldNotInputClif input) (oldNotInputResults input) rfl (oldNotInputMapped input) (oldNotInputRecorded input) (oldNotInputEmitted input) (oldNotInputSelectedId input)
      self restrictedDFG guarded sourceStep
  exact ⟨(oldNotInputResult input),(oldNotInputEvent input),(oldNotInputRecord input),ρ',fr',(oldNotInputRun input),(oldNotInputEvents input),(oldNotInputRecords input),execution,sourceStep,sourceHeld⟩

theorem base_source_witness :
    ∃ (result : Result) (event : BlockScanEvent) (record : ScanRecord) (ρ' : Nat → CV) (fr' : Clif.Frame),
      Stock.lower (formFunction .registers) = .ok result ∧
      event ∈ result.blockScans.toList ∧ record ∈ event.output.records ∧
      PRun (fun _ => True) ispec (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) (formRegs .registers) ρ' ∧
      SourceInstResult Clif.Env.empty {funcs := []} event.ctx record.inst
        (oldRrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf (formFunction .registers) (availIn (formFunction .registers) result.ctx) 0 1)
        event.ctx fr' (fun k => ρ' (aliasNum result.final.alias k)) := by
  obtain ⟨input⟩ := stock_lower_logical_record_inputs_witness .registers
  have restrictedDFG := dfgCons_congr (ctx := input.event.ctx) (fr := formFrame .registers)
    (fr' := restrict oldRrFrame (availOf (formFunction .registers)
      (availIn (formFunction .registers) input.result.ctx) 0 0)) rfl rfl (oldRrRestricted input.result.ctx) input.dfg
  have guarded := input.held.mono (fun y (h : Demanded input.record.output.state y ∧ y ∈
    availOf (formFunction .registers) (availIn (formFunction .registers) input.result.ctx) 0 0) => h.1)
  have block : (formFunction .registers).blocks[0]? = some ((formFunction .registers).blocks[0]!) := rfl
  have statement : ((formFunction .registers).blocks[0]!).body[0]? =
      some (⟨[100],.binary .bor .i64 7 31⟩ : Clif.Stmt) := rfl
  have current : input.record.inst = blockStart (formFunction .registers) 0 + 0 := by
    have zero := input.current
    change input.record.inst = 0 at zero
    simpa only [blockStart,List.take_zero,List.map_nil,List.sum_nil,Nat.zero_add] using zero
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  let val : Clif.Val := ⟨Clif.Ty.i64,Clif.Sem.binary .bor (BitVec.ofNat 64 7) (BitVec.ofNat 64 5)⟩
  let fr' : Clif.Frame := { oldRrFrame with regs := oldRrFrame.regs.set 100 val, body := [] }
  have evaluated : instOutcome Clif.Env.empty {funcs := []} oldRrFrame Clif.Mem.empty
      (.binary .bor .i64 7 31) = .ok ([val],Clif.Mem.empty) := rfl
  have sourceStep : SourceInstResult Clif.Env.empty {funcs := []} input.event.ctx input.record.inst
      (oldRrFrame,Clif.Mem.empty) (fr',Clif.Mem.empty) :=
    ⟨input.info,.binary .bor .i64 7 31,[val],oldRrFrame.regs.set 100 val,[],
      input.source,input.clif,by rw [input.results]; rfl,evaluated,by rw [input.results]; rfl,rfl⟩
  obtain ⟨u,v,ρ',getU,getV,execution,value,memory,kept,sourceHeld⟩ :=
    source_from_step input.run (formScope .registers) oldRrDominated input.events input.records
      block statement current .bor input.source input.clif input.results rfl input.mapped
      input.recorded input.emitted input.selectedId self restrictedDFG guarded sourceStep
  exact ⟨input.result,input.event,input.record,ρ',fr',input.run,input.events,input.records,execution,sourceStep,sourceHeld⟩


end Backend.Stock.Proof.LogicalSourceTests
#print axioms Backend.Stock.Proof.LogicalSourceTests.mirrored_source_witness
#print axioms Backend.Stock.Proof.LogicalSourceTests.base_source_witness
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name,_) in env.constants.toList do
    if (env.getModuleIdxFor? name).isSome then continue
    for ax in ← collectAxioms name do
      unless #[``propext,``Classical.choice,``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {name}"
    count := count+1
  logInfo m!"LOGICAL_SOURCE_TRANSFER_WITH_WITNESSES_STANDARD_ONLY {count}"
