import FV.Backend.Proof.StockAcquireConsumerUnaryData
import FV.Backend.Proof.StockCoverageBlock

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm lowerBlockCore assembleOriginalBlock branchArgs

/-- A newly recorded block scan in an actual node transition comes from that
original node's real core call. Synthetic edges never introduce block records. -/
theorem stock_lowerNode_newBlockScan_prepared {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {f : Clif.Function} {params : List Nat} {label : Nat}
    {input output : DriverState} {event : BlockScanEvent}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (member : event ∈ output.blockScans.toList)
    (new : event ∉ input.blockScans.toList) :
    ∃ (bi : Nat) (data : Backend.V) (core : LoweredBlockCore), order.nodes[label]! = .original bi ∧
      Coverage.blockData f f.blocks[bi]!.term = .ok data ∧
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! input.state = .ok core ∧
      event = core.scan ∧ output.state = core.state := by
  cases node : order.nodes[label]! with
  | edge pred k target =>
    unfold lowerNode at run
    simp only [node] at run
    cases args : branchArgs ctx input.state pred k with
    | error e => simp only [args, bind, Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨args, next⟩
      simp only [args, bind, Except.bind, pure, Except.pure] at run
      cases run
      exact False.elim (new member)
  | original bi =>
    let fetchData : Except String Backend.V := match f.blocks[bi]!.term with
      | .tryCall .. | .tryCallIndirect .. => tryCallData f f.blocks[bi]!.term
      | _ => termData (abiTerm f f.blocks[bi]!.term)
    let reject : Bool := (match f.blocks[bi]!.term with | .ret .. => true | _ => false) &&
      (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
    have normal : lowerNode ctx ranges order f params label input = (do
        let data ← fetchData
        if reject then throw "sret parameter is not an entry-block parameter"
        let core ← lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
          data order.successors[label]! input.state
        let block ← assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
          core.outgoing params core.state.uses core.code
        pure { recordCore input core bi ranges[bi]!.2 with
          blocks := input.blocks.set! label block,
          edgeArgs := input.edgeArgs.set! label core.outgoing }) := by
      unfold lowerNode
      simp only [node]
      dsimp only [fetchData, reject]
      split <;> simp_all only [reject] <;> rfl
    rw [normal] at run
    cases dataRun : fetchData with
    | error e => simp only [dataRun, bind, Except.bind] at run; cases run
    | ok data =>
      simp only [dataRun, bind, Except.bind] at run
      split at run
      · cases run
      · cases coreRun : lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
          data order.successors[label]! input.state with
        | error e => simp only [coreRun] at run; cases run
        | ok core =>
          simp only [coreRun] at run
          cases assembled : assembleOriginalBlock ctx f f.blocks[bi]! bi label order.successors[label]!
            core.outgoing params core.state.uses core.code with
          | error e => simp only [assembled] at run; cases run
          | ok block =>
            simp only [assembled, pure, Except.pure] at run
            cases run
            change event ∈ (input.blockScans.push core.scan).toList at member
            simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
            rcases member with old | same
            · exact False.elim (new old)
            · exact ⟨bi, data, core, rfl, dataRun, coreRun, same, rfl⟩


/-- Every newly observed block record in a successful traversal has an actual
earlier, original-node transition and remaining suffix. The core that introduced
the record is the core used by that transition, not a replayed certificate. -/
theorem stock_lowerNodes_newBlockScan_prepared {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {f : Clif.Function} {params labels : List Nat}
    {input output : DriverState} {event : BlockScanEvent}
    (run : labels.foldlM (fun d label => lowerNode ctx ranges order f params label d)
      input = .ok output)
    (member : event ∈ output.blockScans.toList)
    (new : event ∉ input.blockScans.toList) :
    ∃ (earlier suffix : List Nat) (label bi : Nat) (before after : DriverState)
      (data : Backend.V) (core : LoweredBlockCore),
      labels = earlier ++ label :: suffix ∧
      earlier.foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok before ∧
      lowerNode ctx ranges order f params label before = .ok after ∧
      suffix.foldlM (fun d k => lowerNode ctx ranges order f params k d) after = .ok output ∧
      order.nodes[label]! = .original bi ∧
      Coverage.blockData f f.blocks[bi]!.term = .ok data ∧
      lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data order.successors[label]! before.state = .ok core ∧
      event = core.scan ∧ after.state = core.state := by
  induction labels generalizing input with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure] at run
    cases run
    exact False.elim (new member)
  | cons label rest ih =>
    rw [List.foldlM_cons] at run
    cases call : lowerNode ctx ranges order f params label input with
    | error e => simp only [call, bind, Except.bind] at run; cases run
    | ok middle =>
      simp only [call, bind, Except.bind] at run
      by_cases now : event ∈ middle.blockScans.toList
      · obtain ⟨bi, data, core, node, prepared, coreRun, eventEq, stateEq⟩ :=
          stock_lowerNode_newBlockScan_prepared call now new
        exact ⟨[], rest, label, bi, input, middle, data, core,
          rfl, rfl, call, run, node, prepared, coreRun, eventEq, stateEq⟩
      · obtain ⟨earlier, suffix, k, bi, before, after, data, core,
            parts, prefixRun, step, suffixRun, node, prepared, coreRun, eventEq, stateEq⟩ :=
          ih run now
        refine ⟨label :: earlier, suffix, k, bi, before, after, data, core,
          ?_, ?_, step, suffixRun, node, prepared, coreRun, eventEq, stateEq⟩
        · simp only [List.cons_append, parts]
        · simpa only [List.foldlM_cons, call, bind, Except.bind] using prefixRun

/-- A block record retained by successful whole-function lowering has an actual
traversal origin and successful prefix/suffix, in the returned context and order. -/
theorem stock_lower_blockScanOrigin_prepared {f : Clif.Function} {result : Result}
    (run : Stock.lower f = .ok result) {event : BlockScanEvent}
    (member : event ∈ result.blockScans.toList) :
    ∃ (ranges : Array (Nat × Nat)) (params earlier suffix : List Nat)
      (starting finishing before after : DriverState) (label bi : Nat)
      (data : Backend.V) (core : LoweredBlockCore),
      Stock.buildCtx f = .ok (result.ctx, ranges, result.initial) ∧
      blockOrder f = .ok result.order ∧
      starting.state = result.initial ∧ starting.blockScans = #[] ∧
      (Array.range result.order.nodes.size).reverse.toList = earlier ++ label :: suffix ∧
      (Array.range result.order.nodes.size).reverse.toList.foldlM
        (fun d k => lowerNode result.ctx ranges result.order f params k d) starting = .ok finishing ∧
      finishing.state = result.final ∧
      earlier.foldlM (fun d k => lowerNode result.ctx ranges result.order f params k d)
        starting = .ok before ∧
      lowerNode result.ctx ranges result.order f params label before = .ok after ∧
      suffix.foldlM (fun d k => lowerNode result.ctx ranges result.order f params k d)
        after = .ok finishing ∧
      result.order.nodes[label]! = .original bi ∧
      Coverage.blockData f f.blocks[bi]!.term = .ok data ∧
      lowerBlockCore result.ctx result.order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
        data result.order.successors[label]! before.state = .ok core ∧
      event = core.scan ∧ after.state = core.state := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind, Except.bind, pure, Except.pure] at run
    | split at run
  cases run
  rename_i _ _ params _ _ _ _ _ source build _ order ordered _ driver folded
  obtain ⟨earlier, suffix, label, bi, before, after, data, core,
      parts, prefixRun, step, suffixRun, node, prepared, coreRun, eventEq, stateEq⟩ :=
    stock_lowerNodes_newBlockScan_prepared folded member (by simp)
  exact ⟨_, params, earlier, suffix, _, driver, before, after, label, bi, data, core,
    build, ordered, rfl, rfl, parts, folded, rfl, prefixRun, step, suffixRun,
    node, prepared, coreRun, eventEq, stateEq⟩


end Backend.Stock.Proof.Acquire810
