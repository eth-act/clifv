import FV.Opt.Proof.SemSim
import FV.Backend.Proof.StockRecordContext
import FV.Backend.Proof.StockAvailableValues
import FV.Backend.Proof.StockScanSemantics
import FV.Backend.Proof.LowerSim

/-! Source definedness is separate from optional mapped value holding. It is
established by real activation entry and preserved by real source steps, so an
implicit struct-return pointer need not be assumed as a new input certificate. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Backend.Proof.Driver.Fix Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock

def SourceDefinedAt (f : Clif.Function) (ctx : Ctx) (bi j : Nat) (fr : Clif.Frame) : Prop :=
  ∀ x ∈ availOf f (availIn f ctx) bi j, ∃ v,fr.regs x = some v

/-- Original successful function entry defines every initially available source
value, under the original SSA condition, for any retained source context. -/
theorem source_defined_enterFunc {f : Clif.Function} (dominated : Dominated f) (ctx : Ctx)
    {args : List Clif.Val} {cm cm' : Clif.Mem} {fr : Clif.Frame}
    (entered : Clif.enterFunc f args cm = .ok (fr,cm')) : SourceDefinedAt f ctx 0 0 fr := by
  obtain ⟨b,regs,entry,types,paramTypes,set,slots,frame⟩ := Opt.enterFunc_ok entered
  simp only [Clif.Function.entry?,List.head?_eq_getElem?] at entry
  have nodup : (b.params.map (·.1)).Nodup := (List.nodup_append.mp (block_nodup dominated.ssa entry)).1
  intro x available
  obtain ⟨present,_⟩ := (mem_av entry).mp available
  rcases present with parameter | incoming | ⟨j,stm,earlier,_,_⟩
  · obtain ⟨_,v,_,_,value⟩ := setMany_mem set nodup x parameter
    refine ⟨v,?_⟩
    rw [frame]
    exact value
  · have bound := (inFix_fixOk (f := f) (ctx := ctx) (gn := id)).cand 0 x incoming
    omega
  · omega

private theorem statement_results {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {i : Nat} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : i = blockStart f bi + j)
    {info : IInfo} {inst : Clif.Inst}
    (source : event.ctx.insts[i]? = some info) (clif : info.clif = some inst) :
    info.results = stm.results := by
  have globalSource := (stock_lower_record_context run scope events).2.2 _ _ _ source clif
  obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
    label, nodeBi, data, core, build, ordered, initial, empty, parts, folded,
    final, prefixRun, nodeRun, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original, st0, oldBuild, spec, view⟩ := buildCtx_source build
  obtain ⟨other, found, originalClif, results⟩ := spec.facts.stmt bi b j stm block statement
  have actual : original.insts[blockStart f bi + j]? = some info := by
    rw [← view.insts, ← current]; exact globalSource
  cases Option.some.inj (found.symm.trans actual)
  exact results

/-- Actual successful ordinary source steps preserve definedness across the
original availability boundary, including instructions with memory effects. -/
theorem stock_lower_source_defined_step {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {event : BlockScanEvent} {i : Nat} (events : event ∈ result.blockScans.toList)
    {bi j : Nat} {b : Clif.Block} {stm : Clif.Stmt}
    (block : f.blocks[bi]? = some b) (statement : b.body[j]? = some stm)
    (current : i = blockStart f bi + j)
    {env : Clif.Env} {cp : Clif.Program} {fr fr' : Clif.Frame} {cm cm' : Clif.Mem}
    (defined : SourceDefinedAt f result.ctx bi j fr)
    (step : SourceInstResult env cp event.ctx i (fr,cm) (fr',cm')) :
    SourceDefinedAt f result.ctx bi (j+1) fr' := by
  obtain ⟨info,inst,vals,regs,rest,source,clif,body,outcome,set,updated⟩ := step
  dsimp only at updated
  have results := statement_results run scope events block statement current source clif
  have nodup : info.results.Nodup := by rw [results]; exact stmt_nodup dominated.ssa block statement
  intro x available
  rw [updated]
  by_cases new : x ∈ info.results
  · obtain ⟨_,v,_,_,value⟩ := setMany_mem set nodup x new
    exact ⟨v,value⟩
  · have before := available_before_of_after_not_result block statement available (by rwa [← results])
    obtain ⟨v,value⟩ := defined x before
    exact ⟨v,by change regs x = some v; rw [setMany_other set new]; exact value⟩

private theorem view_avail {ctx original : Ctx}
    (view : DFGViewEq ctx original) (f : Clif.Function) :
    availIn f ctx = availIn f original := by
  have args : defArgs ctx = defArgs original := by
    funext x
    simp only [defArgs, Ctx.defInst?, view.valDef, view.insts]
  have users : fUsers ctx = fUsers original := by
    simp only [fUsers, usersN, args, view.valDef]
  have bytes : fInB0 f ctx id = fInB0 f original id := by
    unfold fInB0
    rw [view.valDef]
  have work : fWork0 f ctx id = fWork0 f original id := by
    simp only [fWork0, view.valDef, bytes, args]
  simp only [availIn, inFix_eq, users, bytes, work, view.valDef]

/-- Original source return success supplies its explicit operands; original
source definedness and dominance supply the implicit ABI pointer internally. -/
theorem stock_lower_return_abi_read {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (dominated : Dominated f)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    {b : Clif.Block} (block : f.blocks[event.block]? = some b)
    {xs : List Nat} (ret : b.term = .ret xs)
    {env : Clif.Env} {cp : Clif.Program} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (callers : s.callers = []) (done : Clif.stepTerm env cp s (.ret xs) = .done vals cm)
    (defined : SourceDefinedAt f result.ctx event.block b.body.length s.frame) :
    ∃ extra,s.frame.getMany (xs ++ sretRet f) = .ok (vals ++ extra) := by
  have explicit := ((stepTerm_ret (env := env) (p := cp) (s := s) (xs := xs) callers).2.2 vals cm done).1
  apply getMany_append_of (fr := s.frame) (ys := sretRet f) ?_ explicit
  intro y member
  obtain ⟨ranges,params,earlier,suffix,starting,finishing,before,after,label,bi,data,core,
    build,ordered,initial,empty,parts,folded,final,prefixRun,nodeRun,suffixRun,node,coreRun,eventEq,stateEq⟩ :=
    stock_lower_blockScanOrigin run events
  obtain ⟨original,st0,oldBuild,spec,view⟩ := buildCtx_source build
  have available := (dominated.uses original ranges st0 oldBuild event.block b block).2 y
    (by simp only [ret,abiTerm,termArgs]; exact List.mem_append_right _ member)
  apply defined y
  rw [view_avail view f]
  exact available
end Backend.Stock.Proof
