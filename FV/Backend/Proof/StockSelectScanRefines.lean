import FV.Backend.Proof.StockSourceDFG
import FV.Backend.Proof.StockSelectOriginalSourceValues

/-! Discharge actual select-record scan obligations, carrying the source
position, restricted DFG, demanded values and memory/world relation together. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

abbrev SourcePoint := Nat × Clif.Frame × Clif.Mem

def IndexedSourceInst (env : Clif.Env) (cp : Clif.Program) (f : Clif.Function)
    (ctx : Ctx) (bi : Nat) (i : Nat) (s s' : SourcePoint) : Prop :=
  i = blockStart f bi + s.1 ∧ s'.1 = s.1 + 1 ∧
    SourceInstResult env cp ctx i s.2 s'.2

def GuardedScanRel (f : Clif.Function) (result : Result) (ctx : Ctx) (bi : Nat)
    (MR : MemRelT) (st : State) (s : SourcePoint) (ρ : Nat → CV) (w : Arm.ArmState) : Prop :=
  s.2.1.func = f ∧ DFGCons ctx (restrict s.2.1 (availOf f (availIn f result.ctx) bi s.1)) ∧
    MR s.2.1.slots s.2.2 w ∧
    ValuesHeld (fun x => Demanded st x ∧ x ∈ availOf f (availIn f result.ctx) bi s.1)
      ctx s.2.1 (fun k => ρ (aliasNum result.final.alias k))

private theorem select_operands {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt} (block : f.blocks[bi]? = some b)
    (statement : b.body[j]? = some stm) (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {c x y : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.select ty c x y))
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (step : SourceInstResult env cp event.ctx record.inst (fr,cm) (fr',cm')) :
    ∃ (cty : Clif.Ty) (test : BitVec cty.width) (u v : BitVec ty.width),
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs c cty = .ok test ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs x ty = .ok u ∧
      (restrict fr (availOf f (availIn f result.ctx) bi j)).getAs y ty = .ok v := by
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := step
  cases Option.some.inj (found.symm.trans source)
  cases Option.some.inj (original.symm.trans clif)
  simp only [instOutcome, Clif.evalInst, res_bind_eq_ok, Clif.Res.pure_eq] at evaluated
  obtain ⟨cv, getC, u, getX, v, getY, _⟩ := evaluated
  have getC' : fr.getAs c cv.ty = .ok cv.bits := by
    simp [Clif.Frame.getAs, getC, Clif.Val.as?]
  have available := stock_lower_record_args_available run scope dominated events block statement current source clif
  refine ⟨cv.ty, cv.bits, u, v, ?_, ?_, ?_⟩
  · exact (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := c) (ty := cv.ty) (restrict_regs_of_mem (available c (by simp [Driver.instArgs])))).trans getC'
  · exact (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := x) (ty := ty) (restrict_regs_of_mem (available x (by simp [Driver.instArgs])))).trans getX
  · exact (getAs_congr (fr := fr) (fr' := restrict fr (availOf f (availIn f result.ctx) bi j))
      (x := y) (ty := ty) (restrict_regs_of_mem (available y (by simp [Driver.instArgs])))).trans getY

/-- The real select record discharges its indexed scan obligation. Original
source success derives all operand getters; original dominance/context facts
derive post DFG consistency. No family-execution callback is assumed. -/
theorem stock_lower_select_scan_fall_refines {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : record.inst = blockStart f bi + j)
    {info : IInfo} {ty : Clif.Ty} {c x y z a : Nat}
    (source : event.ctx.insts[record.inst]? = some info) (clif : info.clif = some (.select ty c x y))
    (results : info.results = [z]) (statementResults : stm.results = [z])
    (mapped : event.ctx.valueReg? z = some (.vreg a .int))
    {step : Step} (recorded : record.output.step = some step) (emitted : step.decision = .emitted)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program} :
    ScanFallRefines (IndexedSourceInst env cp f event.ctx bi) isem result.final.alias
      (GuardedScanRel f result event.ctx bi MR) record := by
  intro s s' hsource ρ w held
  obtain ⟨indexed, advance, sourceStep⟩ := hsource
  have position : s.1 = j := Nat.add_left_cancel (indexed.symm.trans current)
  obtain ⟨func, dfg, memory, values⟩ := held
  rw [position] at dfg values
  obtain ⟨cty,test,u,v,getC,getX,getY⟩ := select_operands run scope dominated events block statement current source clif sourceStep
  obtain ⟨d,output,lower,upper,unchanged,execution⟩ := ScalarSelect.stock_lower_select_source_values
    run scope dominated events records block statement current source clif results statementResults mapped
    recorded emitted refines dfg getC getX getY values sourceStep
  obtain ⟨ρ',w',executed,world,post⟩ := execution w
  have postDFG := stock_lower_source_step_dfg run scope dominated events block statement current func dfg sourceStep
  obtain ⟨info',inst,vals,regs,rest,found,original,body,evaluated,written,updated⟩ := sourceStep
  have func' : s'.2.1.func = f := by rw [updated]; exact func
  have slots : s'.2.1.slots = s.2.1.slots := by rw [updated]
  refine ⟨ρ',w',executed,func',?_,?_,?_⟩
  · simpa only [advance,position] using postDFG
  · rw [slots,unchanged]
    exact stable _ _ _ _ world memory
  · simpa only [advance,position] using post.2.2
end Backend.Stock.Proof
