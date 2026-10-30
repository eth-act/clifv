import FV.Backend.Proof.IselTermFactsBase
import FV.Backend.Proof.StockConstantDispatch
import FV.Backend.Proof.CSemRename
import FV.Backend.Proof.RegallocTac

namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

private theorem scan_empty (st : State) (i : Nat) : (scanState st i).base.emitted = #[] := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem scan_next (st : State) (i : Nat) :
    (scanState st i).base.nextVreg = st.base.nextVreg := by
  unfold scanState
  dsimp only
  split <;> rfl

private theorem renamed_defs (aliases : Array (Option Nat)) (m : MInst) :
    vdefs (m.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
      (vdefs m).map (aliasNum aliases) := by
  have aliasRenaming : VRenaming (Backend.lowerFunction.resolve aliases (aliases.size+1)) (aliasNum aliases) := by
    refine ⟨fun n c => resolve_vreg aliases _ n c,?_⟩
    intro r notVirtual
    cases r with
    | vreg n c => exact False.elim (notVirtual n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  unfold vdefs
  rw [operands_mapRegs aliasRenaming]
  cases m.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map,Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl)]
    simp only [List.map_map]
    rfl

/-- Actual constant selection and binding derive the resolved fresh-write
interval used by inherited-value preservation. No code-shape input is assumed. -/
theorem constant_record_fresh_defs {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {ty : Clif.Ty} {imm : BitVec ty.width} {x a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.iconst ty imm))
    (results : info.results = [x]) (mapped : event.ctx.valueReg? x = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted) :
    ∀ m ∈ record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))),
      ∀ key ∈ vdefs m,record.input.base.nextVreg ≤ key ∧ key < record.output.state.base.nextVreg := by
  obtain ⟨receipt⟩ := stock_lower_record_selection run events records recorded emitted
  have context := (stock_lower_record_context run scope events).1
  have chosen := ConstantComplete.selected_rule context source clif receipt.selected
  have count : (program.rulesOf T.lower.id).length = 517 := by
    rw [show T.lower.id = 686 from rfl,data_program.r686]
    rfl
  have enough := receipt.selected.fuelBound
  have matched := receipt.selected.matchedRun
  have evaluated := receipt.selected.rhsRun
  rw [chosen] at matched evaluated
  have semantics : ∀ aliases i,ispec (i.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1))) = ispec i := by
    intro aliases i
    funext us w
    apply ispec_mapRegs
    refine ⟨fun n c => resolve_vreg aliases _ n c,?_⟩
    intro r notVirtual
    cases r with
    | vreg n c => exact False.elim (notVirtual n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  obtain ⟨ty',imm',ms,d,bound,constant,output,binding,boundEq,shape,execution⟩ :=
    stock_iconst_resolved data_program context source clif rfl refines_ispec semantics
      (by omega) (by decide) matched evaluated results mapped
  have bang : event.ctx.insts[record.inst]! = info := by simp [getElem!_def,source]
  have registers : receipt.results = [[.vreg d .int]] := V.regsVec.inj (receipt.output.symm.trans output)
  have actualBinding := receipt.binding
  rw [bang,registers] at actualBinding
  have pair := Prod.mk.inj (Except.ok.inj (actualBinding.symm.trans binding))
  have state : record.output.state = bound := receipt.state.trans pair.1
  have code : record.output.emitted.toList = ms := by
    rw [receipt.code,pair.1,pair.2,Array.append_empty,shape.emitted,scan_empty,Array.empty_append,List.toList_toArray]
  have bounded := stock_lower_blockScanAliasBounds run event events record records
  rw [code]
  intro m member key defined
  obtain ⟨original,rawMember,rfl⟩ := List.mem_map.mp member
  rw [renamed_defs] at defined
  obtain ⟨raw,rawDef,rfl⟩ := List.mem_map.mp defined
  have bounds := shape.defs original rawMember raw rawDef
  have fixed : aliasNum result.final.alias raw = raw := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by simpa only [scan_next] using Nat.le_trans bounded bounds.1)]
    rfl
  rw [fixed,state]
  simpa only [scan_next] using bounds

end Backend.Stock.Proof.Inherited
