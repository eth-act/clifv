import FV.Backend.Proof.StockMemoryStoreNopReturnBody
import FV.Backend.Proof.StockMemoryCfgReturnRefinesAt
import FV.Backend.Proof.StockCfgReturnBlock
import FV.Backend.Proof.StockCfgTraversalScans

namespace Backend.Stock.Memory.StoreRoots
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock Backend.Stock.Proof
open Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore

private theorem assembled_nonentry {ctx : Ctx} {f : Clif.Function} {b : Clif.Block}
    {bi label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {params : List Nat} {uses : Array UseState} {code : Array MInst} {block : VBlock}
    (nonentry : bi ≠ 0)
    (run : assembleOriginalBlock ctx f b bi label targets outgoing params uses code = .ok block) :
    block.insts = code := by
  unfold assembleOriginalBlock at run
  dsimp only at run
  simp only [show (bi == 0) = false from by simp [nonentry],Bool.false_eq_true,ite_false] at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals cases run; rfl

/-- Original store/return syntax derives the placed successor run for every original memory model at instruction zero.
The successful driver supplies scan identity and code placement internally. -/
theorem actual_nonentry_nop_store_return (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true)
    {label bi : Nat} {b : Clif.Block}
    (tag : result.order.nodes[label]? = some (.original bi))
    (source : f.blocks[bi]? = some b) (nonentry : bi ≠ 0)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    (eventBlock : event.block = bi)
    (formats : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    {storeIndex value pointer : Nat} {flags : Clif.MemFlags}
    (statement : b.body[storeIndex]? = some ⟨[],.store kind.sourceOp ty flags value pointer 0⟩)
    (shape : ∀ j stm,b.body[j]? = some stm → j = storeIndex ∨ stm.inst = .nop)
    (ret : b.term = .ret [])
    {pi vi : Nat} {pb vb : Clif.Block} {valueTy : Clif.Ty}
    (pointerBlock : f.blocks[pi]? = some pb) (parameter : pointer ∈ pb.params.map (·.1))
    (valueBlock : f.blocks[vi]? = some vb) (valueParameter : (value,valueTy) ∈ vb.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
    {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR)
    (memorySem : MemRefines F sb syms isem) (memoryOk : MemRelOk F sb syms f MR)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (func : s.frame.func = f) (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (terminal : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx event.block 0 s.frame)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result event.ctx event.block MR event.output.state
      (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR
      s.frame.slots ⟨label,0,ρ,w⟩ (.returned vals mem) := by
  obtain ⟨ranges,params,input,data,core,raw,prelude,coreRun,assembled,build,sizes,prepared,
    actualEvents,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run tag
  have sourceValue : f.blocks[bi]! = b := by
    rw [List.getElem!_eq_getElem?_getD,source]
    rfl
  rw [sourceValue] at coreRun assembled
  have same : core.scan = event := CfgTrace.actual_scan_unique run scope actualEvents events
    (atBlock.trans eventBlock.symm)
  obtain ⟨term,body,split,bodyRun⟩ := stock_nop_store_return_body kind ty run scope dominated
    formats events (by rw [eventBlock]; exact source) statement shape ret pointerBlock parameter
    valueBlock valueParameter width stable (store_refines_of_mem memorySem) memoryOk (env := env) (cp := cp)
  have family : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    obtain ⟨j,found⟩ := List.mem_iff_getElem?.mp member
    rcases shape j stm found with selected | nop
    · subst j
      have equal := Option.some.inj (found.symm.trans statement)
      subst stm
      simp [OrdinaryBody.OrdinaryInst]
    · simp [OrdinaryBody.OrdinaryInst,nop]
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have actualCode : raw.insts.map (·.mapRegs resolve) = event.output.code.map (·.mapRegs resolve) := by
    rw [assembled_nonentry nonentry assembled,CfgReturn.stock_return_core_code ret coreRun,same]
  have finished := OrdinaryBody.actual_ordinary_return_refines_at_block run scope dominated abi family ret
    events split func callers remaining terminal defined returned refines stable bodyRun
    (pre := #[]) (post := #[]) placed (by simpa only [Array.empty_append,Array.append_empty] using actualCode)
    ρ w held
  simpa only [Array.size_empty] using finished

end Backend.Stock.Memory.StoreRoots
