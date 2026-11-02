import FV.Backend.Proof.StockPerEdgeReturnContract
import FV.Backend.Proof.StockCfgReturnBlock

namespace Backend.Stock.Proof.CfgReturnAt
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The actual source's first trap in an original return block becomes the
same machine trap under the actual per-successor semantics. -/
theorem return_block_traps_at {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f) (dominated : Dominated f)
    (family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst)
    {b : Clif.Block} {label bi : Nat} {xs : List Nat} (ret : b.term = .ret xs)
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    (driver : DriverSem isem) {MR : MemRelT} (stable : MRStable F MR)
    {env : Clif.Env} {cp : Clif.Program}
    (spec : CfgReturn.ReturnBlockSpec f result b label bi isem MR env cp)
    {fuel : Nat} {s : Clif.State} {code : Clif.TrapCode}
    (callers : s.callers = []) (remaining : s.frame.body = b.body) (atTerm : s.frame.term = b.term)
    (trapped : Clif.runLoop env cp fuel s = .trapped code)
    {ρ : Nat → CV} {w : Arm.ArmState}
    (held : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR
      spec.core.scan.output.state (0,s.frame,s.mem) ρ w) :
    RunOkABIAt f result.code result.edgeArgs isem MR s.frame.slots
      ⟨label,spec.preludeCode.size,ρ,w⟩ (.trapped code) := by
  obtain ⟨term,body,split,normal,trapping⟩ := MaskBody.actual_body_refines_at_block run scope dominated family
    spec.events spec.split.block refines driver stable (env := env) (cp := cp)
  have localFamily : ∀ stm ∈ b.body,LocalBody.LocalInst stm.inst := by
    intro stm member
    rcases family b (List.mem_of_getElem? spec.split.block) stm member with
      (scalar | ⟨op,ty,x,y,shape⟩) | ⟨ty,x,shape⟩ | shape
    · exact LocalBody.LocalInst.of_pure (HighMulBody.family_pure scalar)
    all_goals simp [LocalBody.LocalInst,shape]
  have sourceTrap := LocalBody.actual_local_source_trap_execution run spec.events split localFamily
    (j := 0) (by omega) (by simpa using remaining) callers (atTerm.trans ret) trapped
  have machineTrap := trapping (0,s.frame,s.mem) code
    (by simpa only [Nat.add_zero,Nat.sub_zero,List.range'_eq_map_range] using sourceTrap) ρ w held
  let resolve := Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)
  have coreCode := CfgReturn.stock_return_core_code ret spec.coreRun
  have pieces : spec.raw.insts.map (·.mapRegs resolve) =
      spec.preludeCode.map (·.mapRegs resolve) ++ body.code.map (·.mapRegs resolve) ++
      term.output.emitted.map (·.mapRegs resolve) := by
    simp only [spec.rawCode,coreCode,split.code,Array.map_append,Array.append_assoc]
  have segment : SegAt {spec.raw with
      insts := spec.raw.insts.map (·.mapRegs resolve)
      params := spec.raw.params.map resolve
      branchArgs := spec.raw.branchArgs.map resolve}
      spec.preludeCode.size (body.code.toList.map (·.mapRegs resolve)) := by
    intro k hk
    have bound : k < body.code.size := by simpa using hk
    rw [pieces,Array.append_assoc,Array.getElem?_append_right (by simpa only [Array.size_map] using Nat.le_add_right spec.preludeCode.size k)]
    simp only [Array.size_map,Nat.add_sub_cancel_left]
    rw [Array.getElem?_append_left (by simpa only [Array.size_map] using bound)]
    simp [bound]
  obtain ⟨offset,i,ops,ρ',w',outs,final,execution,trapCode⟩ := machineTrap
  obtain ⟨path,bound,inst,operands,semantics,arity,control⟩ :=
    seqRun_stop_starAt (edges := result.edgeArgs) spec.placed segment execution
  exact ⟨label,spec.preludeCode.size+offset,ρ',w',_,i,ops,outs,final,path,spec.placed,
    inst,operands,semantics,trapCode⟩

end Backend.Stock.Proof.CfgReturnAt
