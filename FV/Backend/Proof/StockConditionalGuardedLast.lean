module

public import FV.Backend.Proof.StockConditionalGuardedValues

@[expose] public section

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false

/-- The actual source-correct wide parameter branch stops at the last
instruction of its real buffer. The original branch interface stays available. -/
theorem ConditionalBodySpec.parameter_branch_values_last {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {b : Clif.Block} {label bi c : Nat} {yes no : Clif.BlockCall}
    {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem} (refines : Refines F isem)
    {MR : MemRelT} (stable : MRStable F MR) {env : Clif.Env} {cp : Clif.Program}
    (spec : ConditionalBodySpec f result b label bi c yes no isem MR env cp)
    (block : f.blocks[bi]? = some b) (termShape : b.term = .brif c yes no)
    (parameter : result.ctx.defInst? c = none)
    {fr : Clif.Frame} {cm : Clif.Mem} {cty : Clif.Ty} {test : BitVec cty.width}
    (getC : (restrict fr (availOf f (availIn f result.ctx) spec.core.scan.block b.body.length)).getAs c cty = .ok test)
    (width : cty.width = 32 ∨ cty.width = 64) {ρ : Nat → CV} {world : Arm.ArmState}
    (post : GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
      (b.body.length,fr,cm) ρ world) :
    ∃ index inst ops regs prefixWorld endWorld,
      seqRun isem (spec.origin.emission.code.toList.map
        (·.mapRegs (Backend.lowerFunction.resolve result.final.alias (result.final.alias.size+1)))) ρ world =
        some (.stop index inst ops regs prefixWorld [] endWorld (.goto (if test != 0 then 0 else 1))) ∧
      index+1 = spec.origin.emission.code.size ∧
      GuardedScanRel f result spec.core.scan.ctx spec.core.scan.block MR spec.term.output.state
        (b.body.length,fr,cm) regs endWorld ∧
      inst.targets = result.order.successors[label]!.toList ∧ inst.isTerminator = true := by
  obtain ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,guarded,targets,terminal⟩ :=
    spec.parameter_branch_values run scope refines stable block termShape parameter getC width post
  have inv := (stock_lower_record_context run scope spec.events).1
  have ctxEq := (stock_lowerBlockCore_scanOrigin spec.coreRun).2.1
  have parameterHere : spec.core.scan.ctx.defInst? c = none := by rw [ctxEq]; exact parameter
  obtain ⟨calls,source⟩ := spec.parameter_calls block termShape parameter
  have available := restrict_regs_isSome (by rw [getAs_ok getC]; rfl)
  have typed := stock_lower_available_getAs_type run spec.events available post.2.1 getC
  have count : spec.origin.emission.code.size = 1 := by
    rw [spec.origin.emitted]
    have size : spec.origin.emission.state.base.emitted.size = 1 := by
      rcases width with narrow | wide
      · have actual := calls.parameter_wide_emitted_size inv source false (by simpa [narrow] using typed) parameterHere
        simpa only [Array.size_empty,Nat.zero_add] using actual
      · have actual := calls.parameter_wide_emitted_size inv source true (by simpa [wide] using typed) parameterHere
        simpa only [Array.size_empty,Nat.zero_add] using actual
    exact size
  have bound := (List.getElem?_eq_some_iff.mp (seqRun_stop_mem machine).1).1
  simp only [List.length_map,Array.length_toList] at bound
  have last : index+1 = spec.origin.emission.code.size := by omega
  exact ⟨index,inst,ops,regs,prefixWorld,endWorld,machine,last,guarded,targets,terminal⟩

end Backend.Stock.Proof.ConditionalValues
