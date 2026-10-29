module

public import FV.Backend.Proof.StockArithmeticBodyRefines

@[expose] public section

/-! Shared actual-record extraction for pure single-result source bodies. -/
namespace Backend.Stock.Proof.PureBody
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Source syntax determines the statement; actual lowering determines its
emission/omission, result binding and mapped destination. -/
def SourceRecord (f : Clif.Function) (ctx : Ctx) (bi : Nat) (r : ScanRecord) : Prop :=
  ∃ j b stm, f.blocks[bi]? = some b ∧ b.body[j]? = some stm ∧
    r.inst = blockStart f bi + j ∧ ∃ step, r.output.step = some step ∧
      (step.decision = .omitted ∨ step.decision = .emitted ∧ ∃ info x a,
        ctx.insts[r.inst]? = some info ∧ info.clif = some stm.inst ∧
        info.results = [x] ∧ stm.results = [x] ∧ ctx.valueReg? x = some (.vreg a .int))

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

/-- Extract common record facts once, independently of each family's root IDs.
Both hypotheses describe original syntax and are discharged by class proofs. -/
theorem actual_source_records {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} (blocks : f.blocks = [b])
    (quiet : ∀ stm ∈ b.body, colored stm.inst = false)
    (single : ∀ stm ∈ b.body,
      (stm.inst.resultTypes (fun r => (f.extern? r).map (·.sig)) (f.sigDecls.lookup ·)).map List.length = some 1)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList) :
    ∃ term body, SourceBodySplit f event b term body ∧
      ∀ record ∈ body.records, SourceRecord f event.ctx event.block record := by
  obtain ⟨term,body,split,decisions⟩ := stock_lower_pure_body_decisions run scope blocks quiet events
  refine ⟨term,body,split,?_⟩
  intro record member
  obtain ⟨j,stm,statement,current⟩ := split.positions record member
  obtain ⟨step,recorded,decision⟩ := decisions record member
  refine ⟨j,b,stm,split.block,statement,current,step,recorded,?_⟩
  rcases decision with omitted | emitted
  · exact Or.inl omitted
  · obtain ⟨info,source,clif,results⟩ := ArithmeticBody.body_source_info run events split statement current
    have inv := (stock_lower_record_context run scope events).1
    obtain ⟨tys,types,typed,arity⟩ := inv.resTys record.inst info stm.inst source clif
    have one := single stm (List.mem_of_getElem? statement)
    rw [types] at one
    have length : info.results.length = 1 := arity.trans (Option.some.inj one)
    obtain ⟨x,infoResults⟩ : ∃ x, info.results = [x] := by
      cases values : info.results with
      | nil => simp [values] at length
      | cons x rest =>
        cases rest with
        | nil => exact ⟨x,rfl⟩
        | cons y tail => simp [values] at length
    obtain ⟨emission,emissionRun,scan⟩ := stock_emitted_scan
      (scans_execute split.scanned record member) recorded emitted
    have atInst : event.ctx.insts[record.inst]! = info := by
      simp only [Array.getElem!_eq_getD,Array.getD_eq_getD_getElem?,source,Option.getD_some]
    obtain ⟨r,mapped⟩ := ArithmeticBody.emission_result_mapped emissionRun
      (by rw [atInst]; exact infoResults)
    obtain ⟨a,rfl⟩ := inv.valueReg x r mapped
    exact Or.inr ⟨emitted,info,x,a,source,clif,infoResults,results.symm.trans infoResults,mapped⟩

end Backend.Stock.Proof.PureBody
