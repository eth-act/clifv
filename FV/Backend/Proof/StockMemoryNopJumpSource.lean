import FV.Backend.Proof.StockMemoryCfgJumpReturnAt
import FV.Backend.Proof.StockMemoryNopBodySource
import FV.Backend.Proof.StockCfgTraversalDemand

namespace Backend.Stock.Proof.Control
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock Backend.Stock.Proof Backend.Stock.Proof.Control
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original NOP syntax supplies the guarded body required by the actual jump.
The successor can contain memory instructions. No body-execution certificate is an input. -/
theorem nop_jump_body_returns_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    {b targetBlock : Clif.Block} {label bi tl : Nat} {bc : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : JumpBodySpec f result b label bi bc isem MR env cp)
    (nops : ∀ stm ∈ b.body,stm.inst = .nop)
    (tag : result.order.nodes[label]? = some (.original bi))
    (jump : b.term = .jump bc)
    (targetTag : result.order.nodes[spec.target]? = some (.original tl))
    (targetIndex : blockIdx? f bc.block = some tl)
    (target : f.block? bc.block = some targetBlock)
    {next : BlockScanEvent} (nextEvent : next ∈ result.blockScans.toList) (nextBlock : next.block = tl)
    (forward : label < spec.target)
    {vals : List Clif.Val} {outMem : Clif.Mem}
    (continuation : ∀ (fuel : Nat) (s : Clif.State) (ρ : Nat → CV) (w : Arm.ArmState),
      s.frame.func = f → s.callers = [] → s.frame.body = targetBlock.body →
      s.frame.term = targetBlock.term → SourceDefinedAt f result.ctx tl 0 s.frame →
      Clif.runLoop env cp fuel s = .returned vals outMem →
      GuardedScanRel f result next.ctx next.block MR next.output.state (0,s.frame,s.mem) ρ w →
      RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
        ⟨spec.target,0,ρ,w⟩ (.returned vals outMem))
    {fuel : Nat} {s : Clif.State} (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals outMem)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.core.scan.output.state
      (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.returned vals outMem) := by
  have localFamily : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
    intro stm member
    simp [LocalBody.LocalInst,nops stm member]
  have demand := CfgDemand.ordered_scan_demand_of_labels run scope
    (Array.getElem?_eq_some_iff.mp targetTag).1 forward
    (by simp only [getElem!_def,targetTag,Option.getD_some,nextBlock])
    (by simp only [getElem!_def,tag,Option.getD_some,spec.atBlock]) nextEvent spec.events spec.split
  apply jump_body_returns_at_of_body run scope dominated refines driver stable spec localFamily
    ?_ tag jump targetTag targetIndex target nextEvent nextBlock demand continuation
    callers remaining atTerm defined returned held
  intro a a' steps ρ w relation
  obtain ⟨ρ',w',executed,post⟩ := Backend.Stock.Memory.stock_nop_body_of_split run scope dominated
    spec.events spec.split.block nops spec.split a a'
    (by simpa only [sourceBodyIndices,List.reverse_reverse] using steps) ρ w
    (by simpa only [spec.split.state] using relation.1)
  exact ⟨ρ',w',executed,post,by intro x impossible; cases impossible⟩

end Backend.Stock.Proof.Control
