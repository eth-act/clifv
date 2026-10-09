import FV.Backend.Proof.StockDriverBounds

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-- A newly recorded block scan in an actual node transition comes from that
original node's real core call. Synthetic edges never introduce block records. -/
theorem stock_lowerNode_newBlockScan {ctx : Ctx} {ranges : Array (Nat × Nat)}
    {order : Order} {f : Clif.Function} {params : List Nat} {label : Nat}
    {input output : DriverState} {event : BlockScanEvent}
    (run : lowerNode ctx ranges order f params label input = .ok output)
    (member : event ∈ output.blockScans.toList)
    (new : event ∉ input.blockScans.toList) :
    ∃ (bi : Nat) (data : Backend.V) (core : LoweredBlockCore), order.nodes[label]! = .original bi ∧
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
            · exact ⟨bi, data, core, rfl, coreRun, same, rfl⟩


private def originFunction : Clif.Function := {
  name := "node_record_origin"
  sig := {}
  blocks := [{ id := 0, params := [], body := [], term := .jump ⟨0, []⟩ }] }
private def originBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx originFunction).toOption.getD (sinkCtx, #[], sinkState)
private def originOrder : Order := ⟨#[.original 0], #[#[0]]⟩
private def originInput : DriverState := {
  state := originBuilt.2.2
  blocks := Array.replicate 1 default
  edgeArgs := Array.replicate 1 #[]
  schedule := #[]
  scans := #[]
  blockScans := #[]
  rules := #[] }
private def originCall := lowerNode originBuilt.1 originBuilt.2.1 originOrder originFunction [] 0 originInput
private theorem origin_success : originCall.isOk = true := by decide +kernel
private theorem origin_observed : originCall.toOption.map
    (fun d => (d.blocks[0]!.insts, d.blockScans.size)) = some (#[.jump 0], 1) := by decide +kernel

/-- Actual context construction and node lowering emit a jump and introduce a
nonempty scan record. All three premises of the origin theorem are inhabited. -/
theorem stock_lowerNode_newBlockScan_witness :
    Stock.buildCtx originFunction = .ok originBuilt ∧
    ∃ (output : DriverState) (event : BlockScanEvent), originCall = .ok output ∧
      output.blocks[0]!.insts = #[.jump 0] ∧ event ∈ output.blockScans.toList ∧
      event ∉ originInput.blockScans.toList ∧
      ∃ (bi : Nat) (data : Backend.V) (core : LoweredBlockCore),
        originOrder.nodes[0]! = .original bi ∧
        lowerBlockCore originBuilt.1 originOrder originFunction originFunction.blocks[bi]!
          bi originBuilt.2.1[bi]!.1 originBuilt.2.1[bi]!.2 data originOrder.successors[0]!
          originInput.state = .ok core ∧ event = core.scan ∧ output.state = core.state := by
  refine ⟨rfl, ?_⟩
  cases call : originCall with
  | error e => have success := origin_success; simp only [call, Except.isOk] at success; cases success
  | ok output =>
    have observation := origin_observed
    simp only [call, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observation
    have bound : 0 < output.blockScans.size := by omega
    let event := output.blockScans[0]'bound
    have lookup : output.blockScans[0]? = some event := by
      simp only [event, Array.getElem?_eq_getElem bound]
    have member : event ∈ output.blockScans.toList :=
      Array.mem_toList_iff.mpr (Array.mem_of_getElem? lookup)
    have new : event ∉ originInput.blockScans.toList := by simp [originInput]
    have actual : lowerNode originBuilt.1 originBuilt.2.1 originOrder originFunction [] 0
        originInput = .ok output := call
    exact ⟨output, event, rfl, observation.1, member, new,
      stock_lowerNode_newBlockScan actual member new⟩

end Backend.Stock.Proof
