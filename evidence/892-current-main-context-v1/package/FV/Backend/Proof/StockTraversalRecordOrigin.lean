import FV.Backend.Proof.StockNodeRecordOrigin

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- Every newly observed block record in a successful traversal has an actual
earlier, original-node transition and remaining suffix. The core that introduced
the record is the core used by that transition, not a replayed certificate. -/
theorem stock_lowerNodes_newBlockScan {ctx : Ctx} {ranges : Array (Nat × Nat)}
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
      · obtain ⟨bi, data, core, node, coreRun, eventEq, stateEq⟩ :=
          stock_lowerNode_newBlockScan call now new
        exact ⟨[], rest, label, bi, input, middle, data, core,
          rfl, rfl, call, run, node, coreRun, eventEq, stateEq⟩
      · obtain ⟨earlier, suffix, k, bi, before, after, data, core,
            parts, prefixRun, step, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
          ih run now
        refine ⟨label :: earlier, suffix, k, bi, before, after, data, core,
          ?_, ?_, step, suffixRun, node, coreRun, eventEq, stateEq⟩
        · simp only [List.cons_append, parts]
        · simpa only [List.foldlM_cons, call, bind, Except.bind] using prefixRun

private theorem singleton_run {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {f : Clif.Function} {params : List Nat} {label : Nat}
    {input output : DriverState}
    (call : lowerNode ctx ranges order f params label input = .ok output) :
    [label].foldlM (fun d k => lowerNode ctx ranges order f params k d) input = .ok output := by
  simp only [List.foldlM_cons, List.foldlM_nil, call, bind, Except.bind, pure, Except.pure]

/-- A real successful context/node call emits a jump and a block-scan record;
its singleton traversal inhabits all premises and the extracted core origin. -/
theorem stock_lowerNodes_newBlockScan_witness :
    ∃ (ctx : Ctx) (ranges : Array (Nat × Nat)) (order : Order) (f : Clif.Function)
      (input output : DriverState) (event : BlockScanEvent),
      ([0] : List Nat).foldlM (fun d k => lowerNode ctx ranges order f [] k d)
        input = .ok output ∧
      output.blocks[0]!.insts = #[.jump 0] ∧
      event ∈ output.blockScans.toList ∧ event ∉ input.blockScans.toList ∧
      ∃ (earlier suffix : List Nat) (label bi : Nat) (before after : DriverState)
        (data : Backend.V) (core : LoweredBlockCore),
        [0] = earlier ++ label :: suffix ∧
        earlier.foldlM (fun d k => lowerNode ctx ranges order f [] k d) input = .ok before ∧
        lowerNode ctx ranges order f [] label before = .ok after ∧
        suffix.foldlM (fun d k => lowerNode ctx ranges order f [] k d) after = .ok output ∧
        order.nodes[label]! = .original bi ∧
        lowerBlockCore ctx order f f.blocks[bi]! bi ranges[bi]!.1 ranges[bi]!.2
          data order.successors[label]! before.state = .ok core ∧
        event = core.scan ∧ after.state = core.state := by
  obtain ⟨_, output, event, call, insts, member, new, _⟩ :=
    stock_lowerNode_newBlockScan_witness
  change lowerNode _ _ _ _ [] 0 _ = .ok output at call
  have run := singleton_run call
  exact ⟨_, _, _, _, _, output, event, run, insts, member, new,
    stock_lowerNodes_newBlockScan run member new⟩

/-- A block record retained by successful whole-function lowering has an actual
traversal origin and successful prefix/suffix, in the returned context and order. -/
theorem stock_lower_blockScanOrigin {f : Clif.Function} {result : Result}
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
      parts, prefixRun, step, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
    stock_lowerNodes_newBlockScan folded member (by simp)
  exact ⟨_, params, earlier, suffix, _, driver, before, after, label, bi, data, core,
    build, ordered, rfl, rfl, parts, folded, rfl, prefixRun, step, suffixRun,
    node, coreRun, eventEq, stateEq⟩

private def wholeOriginFunction : Clif.Function := {
  name := "whole_driver_record_origin"
  sig := {}
  blocks := [{ id := 0, params := [], body := [], term := .jump ⟨0, []⟩ }] }
private def wholeOriginCall := Stock.lower wholeOriginFunction
private theorem wholeOrigin_success : wholeOriginCall.isOk = true := by decide +kernel
private theorem wholeOrigin_observed : wholeOriginCall.toOption.map
    (fun r => (r.code.blocks[0]!.insts, r.blockScans.size)) = some (#[.jump 0], 1) := by decide +kernel

/-- Whole-function lowering succeeds and emits a jump with a real block record.
The whole-driver origin theorem is applied to this retained record. -/
theorem stock_lower_blockScanOrigin_witness :
    ∃ (result : Result) (event : BlockScanEvent) (label bi : Nat) (core : LoweredBlockCore),
      Stock.lower wholeOriginFunction = .ok result ∧
      result.code.blocks[0]!.insts = #[.jump 0] ∧
      event ∈ result.blockScans.toList ∧
      result.order.nodes[label]! = .original bi ∧ event = core.scan := by
  cases call : wholeOriginCall with
  | error e =>
    have success := wholeOrigin_success
    simp only [call, Except.isOk] at success
    cases success
  | ok result =>
    have observed := wholeOrigin_observed
    simp only [call, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observed
    have bound : 0 < result.blockScans.size := by omega
    let event := result.blockScans[0]'bound
    have lookup : result.blockScans[0]? = some event := by
      simp only [event, Array.getElem?_eq_getElem bound]
    have member : event ∈ result.blockScans.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup)
    have actual : Stock.lower wholeOriginFunction = .ok result := call
    obtain ⟨ranges, params, earlier, suffix, starting, finishing, before, after,
      label, bi, data, core, build, ordered, initial, empty, parts, folded,
      final, prefixRun, step, suffixRun, node, coreRun, eventEq, stateEq⟩ :=
      stock_lower_blockScanOrigin actual member
    exact ⟨result, event, label, bi, core, actual, observed.1, member, node, eventEq⟩

end Backend.Stock.Proof
