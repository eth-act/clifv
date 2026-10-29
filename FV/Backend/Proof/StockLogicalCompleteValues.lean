module

public import FV.Backend.Proof.StockLogicalDispatch
public import FV.Backend.Proof.StockLogicalSourceTransfer
public import FV.Backend.Proof.StockLogicalExtrSourceTransfer

@[expose] public section

namespace Backend.Stock.Proof.LogicalComplete
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
open LogicalSelected
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Every actual retained binary logical record executes its original source
step. All eleven first-match roots are discharged internally: ordinary logical
operations, both NOT operand orders, and both EXTR mirrors. Callers supply no
selected-root certificate and retain the original source availability guard. -/
theorem record_source_from_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    (kind : Kind) {info : IInfo} {x y z a : Nat} {ty : Clif.Ty}
    (source : event.ctx.insts[record.inst]? = some info)
    (clif : info.clif = some (.binary kind.cop ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {fr : Clif.Frame} {ρ : Nat → CV}
    (dfg : DFGCons event.ctx (restrict fr (availOf f (availIn f result.ctx) bi j)))
    (held : ValuesHeld (fun v => Demanded record.output.state v ∧
      v ∈ availOf f (availIn f result.ctx) bi j) event.ctx fr (fun k => ρ (aliasNum result.final.alias k)))
    {env : Clif.Env} {cp : Clif.Program} {fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (sourceStep : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (u v : BitVec ty.width) (ρ' : Nat → CV),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v ∧ PRun F isem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size + 1)))) ρ ρ' ∧
      VHolds ⟨ty,Clif.Sem.binary kind.cop u v⟩ (ρ' record.input.base.nextVreg) ∧
      cm' = cm ∧
      (∀ n, n ≠ record.input.base.nextVreg → ρ' n = ρ n) ∧
      ValuesHeld (fun y => Demanded record.input y ∧
        y ∈ availOf f (availIn f result.ctx) bi (j + 1)) event.ctx
          fr'
          (fun k => ρ' (aliasNum result.final.alias k)) := by
  have inventory := record_selected_rule_ids run scope events records kind source clif recorded emitted
  obtain ⟨id,last,member⟩ : ∃ id, step.rules.getLast? = some id ∧ id ∈ candidateIds kind := by
    simpa only [Option.any_eq_true,List.contains_iff_mem] using inventory
  cases kind with
  | band =>
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact not_source_from_step run scope dominated events records block statement current .band true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact not_source_from_step run scope dominated events records block statement current .band false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact source_from_step run scope dominated events records block statement current .band
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
  | bor =>
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact LogicalExtr.source_from_step run scope dominated false events records block statement current
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact LogicalExtr.source_from_step run scope dominated true events records block statement current
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact not_source_from_step run scope dominated events records block statement current .bor true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact not_source_from_step run scope dominated events records block statement current .bor false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact source_from_step run scope dominated events records block statement current .bor
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
  | bxor =>
    simp only [candidateIds,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact not_source_from_step run scope dominated events records block statement current .bxor true
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact not_source_from_step run scope dominated events records block statement current .bxor false
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep
    · exact source_from_step run scope dominated events records block statement current .bxor
        source clif results statementResults mapped recorded emitted last refines dfg held sourceStep

end Backend.Stock.Proof.LogicalComplete
