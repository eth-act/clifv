import FV.Backend.Proof.StockCfgReturnRefinesAt
import FV.Backend.Proof.StockCfgReturnBlock

namespace Backend.Stock.Proof.CfgReturnAt
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- The same actual return core executes under per-successor VCode semantics.
Its retained assembly supplies placement; the existing source/body theorems
supply all emitted rule semantics without a new program certificate. -/
theorem return_block_returns_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (abi : sigAbiOk f.sig = true)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi : Nat} {xs : List Nat} (ret : b.term = .ret xs)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : CfgReturn.ReturnBlockSpec f result b label bi isem MR env cp)
    {fuel : Nat} {s : Clif.State} {vals : List Clif.Val} {cm : Clif.Mem}
    (func : s.frame.func = f) (callers : s.callers = [])
    (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (defined : SourceDefinedAt f result.ctx spec.core.scan.block 0 s.frame)
    (returned : Clif.runLoop env cp fuel s = .returned vals cm)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR
      spec.core.scan.output.state (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.returned vals cm) := by
  obtain ⟨term,body,split,normal,trapping⟩ := MaskBody.actual_body_refines_at_block run scope dominated family
    spec.events spec.split.block refines driver stable (env := env) (cp := cp)
  have localFamily : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
    intro stm member
    rcases family b (List.mem_of_getElem? spec.split.block) stm member with
      (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
    · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
    all_goals simp [LocalBody.LocalInst,shape]
  have coreCode := CfgReturn.stock_return_core_code ret spec.coreRun
  have code : spec.raw.insts.map (·.mapRegs
      (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) =
      spec.preludeCode.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++
      spec.core.scan.output.code.map (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1))) ++ #[] := by
    simp only [spec.rawCode,coreCode,Array.map_append,Array.append_empty]
  have finished := actual_local_return_refines_at_block run scope dominated abi localFamily ret spec.events split
    func callers remaining atTerm defined returned refines stable normal spec.placed code ρ w held
  simpa only [Array.size_map] using finished

end Backend.Stock.Proof.CfgReturnAt
