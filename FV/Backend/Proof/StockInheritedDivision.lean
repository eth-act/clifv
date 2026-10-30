import FV.Backend.Proof.StockInheritedBody
import FV.Backend.Proof.StockInheritedFrame

namespace Backend.Stock.Proof.Inherited
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- All existing original signed/unsigned division and remainder forms preserve
inherited values on normal execution, including arbitrary narrow operands and
all selected forms. This reuses their complete source execution and frame. -/
theorem division_scan_carry_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block+j)
    (op : Clif.DivOp) {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div op ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {needed : Nat → Prop}
    (available : ∀ v,needed v → v ∈ availOf f (availIn f result.ctx) event.block 0)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx event.block) isem result.final.alias
      (CarryRel f result event.ctx event.block MR needed) record := by
  have normal := stock_lower_div_scan_fall_refines run scope dominated events records split.block
    statement current op source clif results statementResults mapped recorded emitted refines stable (env := env) (cp := cp)
  intro s s' sourceStep ρ w held
  obtain ⟨ρ',w',executed,post⟩ := normal s s' sourceStep ρ w held.1
  have position : s.1 = j := Nat.add_left_cancel (sourceStep.1.symm.trans current)
  have dfg := held.1.2.1
  have values := held.1.2.2.2
  rw [position] at dfg values
  obtain ⟨u,v,d,q,output,bounds,division,unchanged,execution⟩ :=
    ScalarDiv.stock_lower_div_source_by_instruction run scope dominated events records split.block statement current
      source clif results statementResults mapped recorded emitted refines dfg values sourceStep.2.2
  obtain ⟨ρ2,w2,executed2,world,value,kept,values2⟩ := execution w
  have same := Option.some.inj (executed2.symm.trans executed)
  injection same with regsEq worldEq
  rw [regsEq] at kept
  exact ⟨ρ',w',executed,post,record_frame_carry run scope dominated events split records statement current
    sourceStep.2.2 available kept held.2⟩

/-- Adding carry to the normal invariant preserves the original first-trap
contract, including zero divisors and signed overflow. -/
theorem division_scan_carry_trap_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {b : Clif.Block} {term : ScanRecord} {body : BlockScan}
    (split : SourceBodySplit f event b term body) {j : Nat} {stm : Clif.Stmt}
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f event.block+j)
    {op : Clif.DivOp} {info : IInfo} {ty : Clif.Ty} {x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.div op ty x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {needed : Nat → Prop} {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} {env : Clif.Env} {cp : Clif.Program} :
    LocalScanTrapRefines (LocalBody.IndexedSourceTrap env cp f event.ctx event.block)
      isem result.final.alias (CarryRel f result event.ctx event.block MR needed) record := by
  have actual : MixedDivRecord f event.ctx event.block record :=
    .division split.block statement current source clif results statementResults mapped recorded emitted
  intro s code failed ρ w held
  exact actual.trap_refines run scope dominated events records refines s code failed ρ w held.1

end Backend.Stock.Proof.Inherited
