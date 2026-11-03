import FV.E2E.StockMemoryStorePairedBody
import FV.E2E.StockMemoryPairedReturnEdgeBody
import FV.Backend.Proof.StockCfgReturnBlock
import FV.Backend.Proof.StockCfgTraversalScans

namespace E2E.StockMemory.StoreRoots
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

/-- Original store/return syntax derives the placed successor run at instruction zero.
The successful driver supplies scan identity and code placement internally. -/
theorem actual_nonentry_paired_store_return (kind : Kind) (ty : Clif.Ty) {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true)
    {label bi : Nat} {b : Clif.Block}
    (tag : result.order.nodes[label]? = some (.original bi))
    (source : f.blocks[bi]? = some b) (nonentry : bi ≠ 0)
    {event : BlockScanEvent} (events : event ∈ result.blockScans.toList)
    (eventBlock : event.block = bi)
    (formats : ∀ b ∈ f.blocks,∀ stm ∈ b.body,CastComplete.MemoryFormat stm.inst)
    {value pointer : Nat} {flags : Clif.MemFlags}
    (singleton : b.body = [⟨[],.store kind.sourceOp ty flags value pointer 0⟩])
    (ret : b.term = .ret [])
    {pi vi : Nat} {pb vb : Clif.Block} {valueTy : Clif.Ty}
    (pointerBlock : f.blocks[pi]? = some pb) (parameter : pointer ∈ pb.params.map (·.1))
    (valueBlock : f.blocks[vi]? = some vb) (valueParameter : (value,valueTy) ∈ vb.params)
    (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits)
    {Γ : Rel} {c : BitVec 64} {D : BitVec 64 → Prop} {fc : FnCtx} {X : ExtSem}
    (slot : fc.slotBase = Γ.slotOff)
    (symbols : ∀ n a,Γ.syms n = some a → X.sym n 0 = BitVec.ofNat 64 a)
    (tls : XTls Γ.F X)
    {env : Clif.Env} {cp : Clif.Program} {fuel : Nat} {s : Clif.State}
    (func : s.frame.func = f) (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (terminal : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx event.block 0 s.frame)
    {vals : List Clif.Val} {mem : Clif.Mem}
    (returned : Clif.runLoop env cp fuel s = .returned vals mem)
    {ρ : Nat → CV} {q : W2}
    (held : PairedScanRel f result event.ctx event.block Γ c D event.output.state
      (0,s.frame,s.mem) ρ q) :
    RunOkABIAt f result.code result.edgeArgs (pairSem (csem Γ.F fc X)) (MRP Γ f c D)
      s.frame.slots ⟨label,0,ρ,q⟩ (.returned vals mem) := by
  obtain ⟨ranges,params,input,data,core,raw,prelude,coreRun,assembled,build,sizes,prepared,
    actualEvents,atBlock,rawCode,placed⟩ := stock_lower_original_block_scan_assembly run tag
  have sourceValue : f.blocks[bi]! = b := by
    rw [List.getElem!_eq_getElem?_getD,source]
    rfl
  rw [sourceValue] at coreRun assembled
  have same : core.scan = event := CfgTrace.actual_scan_unique run scope actualEvents events
    (atBlock.trans eventBlock.symm)
  obtain ⟨term,body,split,bodyRun⟩ := stock_single_store_return_paired_body kind ty run scope dominated
    formats events (by rw [eventBlock]; exact source) singleton ret pointerBlock parameter
    valueBlock valueParameter width slot symbols tls (Γ := Γ) (c := c) (D := D) (env := env) (cp := cp)
  have family : ∀ stm ∈ b.body,OrdinaryBody.OrdinaryInst stm.inst := by
    intro stm member
    have same : stm = ⟨[],.store kind.sourceOp ty flags value pointer 0⟩ := by
      simpa only [singleton,List.mem_singleton] using member
    subst stm
    simp [OrdinaryBody.OrdinaryInst]
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have actualCode : raw.insts.map (·.mapRegs resolve) = event.output.code.map (·.mapRegs resolve) := by
    rw [assembled_nonentry nonentry assembled,CfgReturn.stock_return_core_code ret coreRun,same]
  have finished := actual_ordinary_paired_return_refines_at_block run scope dominated abi family ret
    events split func callers remaining terminal defined returned tls bodyRun
    (pre := #[]) (post := #[]) placed (by simpa only [Array.empty_append,Array.append_empty] using actualCode)
    ρ q held
  simpa only [Array.size_empty] using finished

end E2E.StockMemory.StoreRoots
