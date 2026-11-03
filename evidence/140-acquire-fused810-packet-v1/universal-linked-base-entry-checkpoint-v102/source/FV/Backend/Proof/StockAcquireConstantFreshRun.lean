import FV.Backend.Proof.StockAcquireConstantEmptyMarks
import FV.Backend.Proof.StockAcquireFrozenSourceFrame

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem resolved_defs (aliases : Array (Option Nat)) (inst : MInst) :
    vdefs (inst.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
      (vdefs inst).map (aliasNum aliases) := by
  have rename : VRenaming (Backend.lowerFunction.resolve aliases (aliases.size+1)) (aliasNum aliases) := by
    refine ⟨fun n cls => resolve_vreg aliases _ n cls,?_⟩
    intro reg real
    cases reg with
    | vreg n cls => exact False.elim (real n cls rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  unfold vdefs
  rw [operands_mapRegs rename]
  cases actual : inst.operands with
  | error e => rfl
  | ok operands =>
    simp only [Except.map,Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl)]
    simp only [List.map_map]
    rfl

/-- Every actual constant chunk has fresh definitions and executes for arbitrary registers.
The proof evaluates no source instruction after a delayed fault. -/
theorem stock_lower_constant_fresh_run {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (semantics : ∀ aliases i,isem (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1))) = isem i) :
    (∀ inst ∈ record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs inst,record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg) ∧
    ∀ regs,∃ nextRegs,PRun F isem (record.output.emitted.toList.map
      (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) regs nextRegs := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have context := (stock_lower_record_context run scope events).1
  have chosen := ConstantComplete.selected_rule context source clif receipt.selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686];rfl
  have enough := receipt.selected.fuelBound
  have matched := receipt.selected.matchedRun
  have evaluated := receipt.selected.rhsRun
  rw [chosen] at matched evaluated
  obtain ⟨_,_,code,dest,bound,_,outEq,binding,boundEq,shape,execute⟩ :=
    stock_iconst_resolved data_program context source clif rfl refines semantics
      (by omega) (by decide) matched evaluated results mapped
  have evaluatedOut := evaluated.trans (congrArg (fun value : V =>
    (Except.ok (some value,receipt.next,receipt.selected.rhsTrace) :
      Except Err (Option V × State × Array RuleId))) outEq)
  have root := receipt.rootRun
  rw [outEq] at root
  obtain ⟨actual,actualRun,actualState,actualCode,_⟩ := stock_iconst_emission_alias data_program
    source results mapped rfl matched evaluatedOut root
  obtain ⟨observed,observedRun,scanEq⟩ := stock_emitted_scan
    (stock_fence_record_execute run events records) recorded emitted
  have same : observed = actual := Except.ok.inj (observedRun.symm.trans actualRun)
  rw [same] at scanEq
  have boundBase : bound.base = receipt.next.base := by rw [boundEq]
  have codeEq : record.output.emitted.toList = code := by
    rw [scanEq]
    change actual.code.toList = code
    rw [actualCode,← boundBase,shape.emitted]
    have empty : (scanState record.input record.inst).base.emitted = #[] := by
      unfold scanState
      dsimp only
      split <;> rfl
    rw [empty,Array.empty_append,List.toList_toArray]
  have outputBase : record.output.state.base = bound.base := by
    rw [scanEq]
    change actual.state.base = bound.base
    rw [actualState,boundBase]
  have inputFrontier : (scanState record.input record.inst).base.nextVreg = record.input.base.nextVreg := by
    unfold scanState
    dsimp only
    split <;> rfl
  have aliases := stock_lower_blockScanAliasBounds run event events record records
  constructor
  · intro inst member key defined
    rw [codeEq] at member
    obtain ⟨raw,present,rfl⟩ := List.mem_map.mp member
    rw [resolved_defs] at defined
    obtain ⟨rawKey,rawDef,rfl⟩ := List.mem_map.mp defined
    have interval := shape.defs raw present rawKey rawDef
    have identity : aliasNum result.final.alias rawKey = rawKey := by
      apply chaseF_none
      rw [Array.getElem?_eq_none (by rw [inputFrontier] at interval;omega)]
      rfl
    rw [identity,outputBase]
    simpa only [inputFrontier] using interval
  · intro regs
    obtain ⟨nextRegs,executed,_,_⟩ := execute result.final.alias aliases regs
    exact ⟨nextRegs,by simpa only [codeEq] using executed⟩

end Backend.Stock.Proof.Acquire810
