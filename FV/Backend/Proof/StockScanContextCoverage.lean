import FV.Backend.Proof.StockRecordFormCoverage

namespace Backend.Stock.Proof.Coverage.Result
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore assembleOriginalBlock branchArgs

private theorem clean_build {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  intro i info found
  change ctx.insts[i]? = some info at found
  rw [view.insts] at found
  exact Cov.clean_of_build legacy i info found

private theorem clean_data {f : Clif.Function} {ctx : Ctx}
    (clean : Clean (sourceIdentityCtx ctx)) {term : Clif.Terminator} {data : V}
    (prepared : Coverage.blockData f term = .ok data) (ti : Nat) (trs : List Reg × List Reg) :
    Clean (sourceIdentityCtx {Driver.termCtx ctx ti data with tryRegs := trs}) := by
  cases term <;> simp only [Coverage.blockData] at prepared
  all_goals first
    | exact clean_tryCtx clean prepared ti trs
    | exact clean_termCtx clean prepared ti

private theorem node_contexts {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params : List Nat} {label : Nat} {input output : DriverState}
    (clean : Clean (sourceIdentityCtx ctx))
    (kept : ∀ event ∈ input.blockScans.toList,Clean (sourceIdentityCtx event.ctx))
    (run : lowerNode ctx ranges order f params label input = .ok output) :
    ∀ event ∈ output.blockScans.toList,Clean (sourceIdentityCtx event.ctx) := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    obtain ⟨⟨args,next⟩,call,done⟩ := Except.bind_ok run
    cases done
    exact kept
  | original bi =>
    have normalized : lowerNode ctx ranges order f params label input = (do
        let data ← Coverage.blockData f f.blocks[bi]!.term
        if (match f.blocks[bi]!.term with | .ret .. => true | _ => false) &&
            (sretRet f).isEmpty && sigRets f.sig != f.sig.returns then
          throw "sret parameter is not an entry-block parameter"
        else do
          let core ← lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
            data order.successors[label]! input.state
          let block ← assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
            core.outgoing params core.state.uses core.code
          pure {recordCore input core bi ranges[bi]!.2 with
            blocks := input.blocks.set! label block,edgeArgs := input.edgeArgs.set! label core.outgoing}) := by
      unfold lowerNode
      simp only [node]
      cases f.blocks[bi]!.term <;>
        cases (sretRet f).isEmpty <;> cases (sigRets f.sig != f.sig.returns) <;> rfl
    rw [normalized] at run
    obtain ⟨data,prepared,rest⟩ := Except.bind_ok run
    change Coverage.blockData f f.blocks[bi]!.term = .ok data at prepared
    repeat' first
      | (solve | simp only [throw,throwThe,MonadExceptOf.throw] at rest; cases rest)
      | (solve |
          obtain ⟨core,coreRun,rest⟩ := Except.bind_ok rest
          obtain ⟨block,assembled,done⟩ := Except.bind_ok rest
          cases done
          intro event member
          change event ∈ (input.blockScans.push core.scan).toList at member
          simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
          rcases member with old | rfl
          · exact kept event old
          · rw [(stock_lowerBlockCore_scanOrigin coreRun).2.1]
            exact clean_data clean prepared _ _)
      | split at rest

private theorem nodes_contexts {ctx : Ctx} {ranges : Array (Nat × Nat)} {order : Order}
    {f : Clif.Function} {params labels : List Nat} {input output : DriverState}
    (clean : Clean (sourceIdentityCtx ctx))
    (kept : ∀ event ∈ input.blockScans.toList,Clean (sourceIdentityCtx event.ctx))
    (run : labels.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output) :
    ∀ event ∈ output.blockScans.toList,Clean (sourceIdentityCtx event.ctx) := by
  induction labels generalizing input with
  | nil => cases run; exact kept
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    obtain ⟨middle,first,last⟩ := Except.bind_ok run
    exact ih (node_contexts clean kept first) last

private theorem origin {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ (ranges : Array (Nat × Nat)) (params : List Nat) (starting finishing : DriverState),
      Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) ∧ starting.blockScans = #[] ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d) starting = .ok finishing ∧
      result.blockScans = finishing.blockScans := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,_,_,_,by assumption,rfl,by assumption,rfl⟩

/-- Every actual retained scan context has clean source/terminator data. Real
context construction, original/critical-node insertion and the complete actual
reverse traversal derive this property, including TryCall data/reservations.
No caller context-data certificate or extra source acceptance check is needed. -/
theorem stock_lower_scan_context_clean {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (events : event ∈ result.blockScans.toList) : Clean (sourceIdentityCtx event.ctx) := by
  obtain ⟨ranges,params,starting,finishing,build,empty,folded,scans⟩ := origin run
  have kept : ∀ event ∈ starting.blockScans.toList,Clean (sourceIdentityCtx event.ctx) := by
    rw [empty]
    intro event member
    cases member
  rw [scans] at events
  exact nodes_contexts (clean_build build) kept folded event events

/-- Original Stock scope and actual source-record membership suffice for
covered forms and ordinary SpillInstOk. Context cleanliness, mapped registers,
actual scan execution and binding copies are all derived internally. -/
theorem stock_lower_source_record_form_coverage_original {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) (scope : LowerScope f)
    {event : BlockScanEvent} {record : ScanRecord}
    (events : event ∈ result.blockScans.toList) (records : record ∈ event.output.records)
    {info : IInfo} {inst : Clif.Inst} (source : event.ctx.insts[record.inst]? = some info)
    (original : info.clif = some inst) :
    ∀ i ∈ record.output.emitted.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) :=
  stock_lower_source_record_form_coverage run scope events records (stock_lower_scan_context_clean run events) source original

end Backend.Stock.Proof.Coverage.Result
