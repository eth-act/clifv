import FV.Backend.Proof.StockSSAScanConnection
import FV.Backend.Proof.StockEdgeAliasFrame
import FV.Backend.Proof.StockBlockRanges

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
attribute [local irreducible] Isle.Aarch64.program

private theorem named_entry {ctx : Ctx} {term : String} {args : List V}
    {st next : State} {out : Option V} {trace : List RuleId} {key : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c)
    (h : Stock.runTerm ctx term args st = .ok (out, next, trace)) :
    (next.alias[key]?).join = (st.alias[key]?).join := by
  unfold Stock.runTerm at h
  cases hr : Isle.Interp.run program (Stock.sem ctx) {} term args st with
  | error e => rw [hr] at h; cases h
  | ok result =>
    rw [hr] at h
    cases h
    unfold Isle.Interp.run at hr
    cases ht : program.termByName? term with
    | none => simp only [ht] at hr; cases hr
    | some t =>
      simp only [ht] at hr
      cases ha : (applyTerm program (Stock.sem ctx) {} (Config.fuel ({} : Config))
          t.ret t.id args).run (st, #[]) with
      | error e => simp only [ha, bind, Except.bind] at hr; cases hr
      | ok result =>
        rcases result with ⟨out, next, trace⟩
        simp only [ha, bind, Except.bind, pure, Except.pure] at hr
        cases hr
        exact stock_apply_aliasEntry payloads ha


private theorem source_payloads_apart {f : Clif.Function} {source ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State} {slot x key : Nat}
    (build : Stock.buildCtx f = .ok (source, ranges, initial))
    (mapped : source.valueReg? x = some (.vreg key .int))
    (reserved : ctx.tryRegs = initial.tryRegs[slot]!) :
    ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c := by
  intro r member c same
  rw [reserved] at member
  cases entry : initial.tryRegs[slot]? with
  | none =>
    simp only [getElem!_def, entry] at member
    change r ∈ ([] : List Reg) at member
    cases member
  | some rs =>
    have mem : r ∈ rs.1 ++ rs.2 := by
      apply List.mem_append.mpr
      right
      simpa only [getElem!_def, entry, Option.getD_some] using member
    have separate := buildCtx_valueReservedDisjoint build x (.vreg key .int)
      mapped slot rs entry r mem
    obtain ⟨k, reg, _⟩ := buildCtx_reservedBelow build slot rs entry r mem
    subst r
    cases reg
    exact separate rfl

theorem stock_emitBranch_aliasEntry {ctx : Ctx} {f : Clif.Function} {t : Clif.Terminator}
    {bi ti : Nat} {targets : Array Nat} {input : State} {output : BranchEmission} {key : Nat}
    (payloads : ∀ r ∈ ctx.tryRegs.2, ∀ c, r ≠ .vreg key c)
    (run : emitBranch ctx f t bi ti targets input = .ok output) :
    (output.state.alias[key]?).join = (input.alias[key]?).join := by
  unfold emitBranch at run
  dsimp only at run
  let before := { input with current := some ti, color := none, base.emitted := #[] }
  change ((do
    let (out, next, fired) ← Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before
    if out.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t targets next.base.emitted
    pure ⟨next, code, ⟨bi, ti, .emitted, before, next, [], fired, code⟩, fired⟩) : Except String BranchEmission) = .ok output at run
  cases root : Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before with
  | error e => simp only [root, bind, Except.bind] at run; cases run
  | ok result =>
    rcases result with ⟨out, next, fired⟩
    simp only [root, bind, Except.bind] at run
    split at run
    · cases run
    · cases code : branchCode f t targets next.base.emitted with
      | error e => simp only [code] at run; cases run
      | ok instructions =>
        simp only [code, pure, Except.pure] at run
        cases run
        have same := named_entry (st := before) payloads root
        exact same

/-- Actual original-block lowering preserves a definition's alias when lowering
another source block. All scan exclusions come from source SSA and real ranges. -/
theorem stock_lowerBlockCore_other_aliasEntry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {x key owner ownerBlock bi : Nat} {info : IInfo}
    (definition : ctx.insts[owner]? = some info) (result : x ∈ info.results)
    (mapped : ctx.valueReg? x = some (.vreg key .int))
    {first second : Clif.Block} (left : f.blocks[ownerBlock]? = some first)
    (right : f.blocks[bi]? = some second) (distinct : ownerBlock ≠ bi)
    {owned : Nat × Nat} {start stop : Nat}
    (firstRange : ranges[ownerBlock]? = some owned)
    (secondRange : ranges[bi]? = some (start, stop))
    (ownerLower : owned.1 ≤ owner) (ownerUpper : owner < owned.2)
    {order : Order} {data : V} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (reservations : input.tryRegs = initial.tryRegs)
    (run : lowerBlockCore ctx order f second bi start stop data targets input = .ok output) :
    (output.state.alias[key]?).join = (input.alias[key]?).join := by
  let ti := stop - 1
  let selected := { Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]! }
  let branch : Bool := match second.term with | .ret .. | .trap .. | .returnCall .. => false | _ => true
  let branchCall : Except String (Option BranchEmission) :=
    if branch then some <$> emitBranch selected f second.term bi ti targets input else pure none
  have payloads : ∀ r ∈ selected.tryRegs.2, ∀ c, r ≠ .vreg key c :=
    source_payloads_apart (slot := ti) build mapped (by simp only [selected, reservations])
  have branchKeeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      (((br.map (·.state)).getD input).alias[key]?).join = (input.alias[key]?).join := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch selected f second.term bi ti targets input with
      | error e => simp only [emitted, Functor.map, Except.map] at call; cases call
      | ok e =>
        simp only [emitted, Functor.map, Except.map] at call
        cases call
        exact stock_emitBranch_aliasEntry payloads emitted
    · cases call; rfl
  have noRevisit : owner ∉ (((Array.range (stop - start)).map (start + ·)).reverse.toList) :=
    stock_buildCtx_other_block_indices build left right distinct firstRange secondRange ownerLower ownerUpper
  have normal : lowerBlockCore ctx order f second bi start stop data targets input = (do
      let br ← branchCall
      let (next, outgoing) ← collectOutgoing ctx order bi targets (br.map (·.state) |>.getD input)
      let before := { next with color := some next.endColor[bi]! }
      let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
      let body ← scanBlock selected bi ti branch indices before
      pure ⟨body.state, body.code ++ (br.map (·.code) |>.getD #[]), outgoing,
        br, ⟨selected, bi, ti, branch, indices, before, body⟩⟩) := by
    unfold lowerBlockCore
    dsimp only [branchCall, branch, selected, ti, Driver.termCtx]
    split <;> simp_all only [branch, selected, ti] <;> rfl
  rw [normal] at run
  cases call : branchCall with
  | error e => simp only [call, bind, Except.bind] at run; cases run
  | ok br =>
    simp only [call, bind, Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (·.state) |>.getD input) with
    | error e => simp only [edges] at run; cases run
    | ok pair =>
      rcases pair with ⟨next, outgoing⟩
      simp only [edges] at run
      let before := { next with color := some next.endColor[bi]! }
      let indices := ((Array.range (stop - start)).map (start + ·)).reverse.toList
      have keeps : (next.alias[key]?).join = (input.alias[key]?).join := by
        rw [stock_collectOutgoing_alias edges]
        exact branchKeeps call
      change (scanBlock selected bi ti branch indices before >>= fun body =>
        pure (⟨body.state, body.code ++ (br.map (·.code) |>.getD #[]), outgoing,
          br, ⟨selected, bi, ti, branch, indices, before, body⟩⟩ : LoweredBlockCore)) = .ok output at run
      cases scan : scanBlock selected bi ti branch indices before with
      | error e => simp only [scan, bind, Except.bind] at run; cases run
      | ok body =>
        simp only [scan, bind, Except.bind, pure, Except.pure] at run
        cases run
        have scanned := stock_scanBlock_sourceAliasEntry
          (ctx := selected) (slot := ti) build mapped (fun _ => rfl)
          (by simp only [selected, reservations])
          (fun i member => stock_buildCtx_term_other_results build ssa data definition result
            (fun eq => noRevisit (eq ▸ member))) scan
        exact scanned.trans keeps

end Backend.Stock.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

private def frameFunction : Clif.Function := {
  name := "other_block_frame"
  sig := {}
  blocks := [
    { id := 7, params := [], body := [⟨[0], .iconst .i64 9⟩], term := .ret [] },
    { id := 9, params := [], body := [], term := .jump ⟨7, []⟩ }] }
private def frameBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx frameFunction).toOption.getD (sinkCtx, #[], sinkState)
private def frameInput : State := { frameBuilt.2.2 with
  base := (frameBuilt.2.2.base.fresh .int).2
  alias := aliasStep #[] (192, 193) }
private def frameOrder : Order := ⟨#[.original 0, .original 1], #[#[], #[0]]⟩
private def frameBlock : Clif.Block := frameFunction.blocks[1]!
private def frameData : Backend.V := (termData frameBlock.term).toOption.getD (.int 0)
private def frameCall := lowerBlockCore frameBuilt.1 frameOrder frameFunction frameBlock
  1 2 3 frameData #[0] frameInput

set_option maxRecDepth 20000 in
private theorem frame_success : frameCall.isOk = true := by
  decide +kernel

end Backend.Stock.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem frame_built : Stock.buildCtx frameFunction = .ok frameBuilt := rfl
private theorem frame_ssa : (valueDefs frameFunction).Nodup := by decide
private theorem frame_definition : frameBuilt.1.insts[0]? =
    some (infoOf frameFunction ⟨[0], .iconst .i64 9⟩) := rfl
private theorem frame_result : (0 : Nat) ∈ (infoOf frameFunction ⟨[0], .iconst .i64 9⟩).results := by decide
private theorem frame_mapping : frameBuilt.1.valueReg? 0 = some (.vreg 192 .int) := rfl
private theorem frame_observed :
    frameCall.toOption.map (fun o => (o.code, o.branch.isSome)) = some (#[.jump 0], true) := by
  decide +kernel

/-- A real jump root and full one-slot backward scan preserve a nonempty alias
for a constant defined in the other block; input is a chosen allocated state. -/
theorem stock_lowerBlockCore_other_aliasEntry_witness :
    Stock.buildCtx frameFunction = .ok frameBuilt ∧
    (valueDefs frameFunction).Nodup ∧
    (∃ output, frameCall = .ok output ∧ output.code = #[.jump 0] ∧
      output.branch.isSome = true ∧ (output.state.alias[192]?).join = some 193) := by
  refine ⟨frame_built, frame_ssa, ?_⟩
  cases call : frameCall with
  | error e => have success := frame_success; simp only [call, Except.isOk] at success; cases success
  | ok output =>
    have observation := frame_observed
    simp only [call, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observation
    refine ⟨output, rfl, observation.1, observation.2, ?_⟩
    have actual : lowerBlockCore frameBuilt.1 frameOrder frameFunction frameBlock
        1 2 3 frameData #[0] frameInput = .ok output := call
    have preserved := stock_lowerBlockCore_other_aliasEntry
      (ctx := frameBuilt.1) (ranges := frameBuilt.2.1) (initial := frameBuilt.2.2)
      (start := 2) (stop := 3) (order := frameOrder) (data := frameData)
      (targets := #[0]) (input := frameInput) (output := output) frame_built frame_ssa
      (owner := 0) (ownerBlock := 0) (bi := 1) frame_definition frame_result frame_mapping
      (first := frameFunction.blocks[0]!) (second := frameBlock) rfl rfl (by decide)
      (owned := (0, 2)) rfl rfl (by decide) (by decide)
      (reservations := rfl) actual
    have entry : (frameInput.alias[192]?).join = some 193 := by decide
    exact preserved.trans entry

private def frameBranchCtx : Ctx :=
  { Driver.termCtx frameBuilt.1 2 frameData with tryRegs := frameInput.tryRegs[2]! }
private def frameBranchCall := emitBranch frameBranchCtx frameFunction frameBlock.term 1 2 #[0] frameInput
private theorem frameBranch_success : frameBranchCall.isOk = true := by decide +kernel
private theorem frameBranch_observed : frameBranchCall.toOption.map (·.code) = some #[.jump 0] := by
  decide +kernel

/-- Actual separately emitted jump lowering preserves the stored source alias. -/
theorem stock_emitBranch_aliasEntry_witness :
    (∃ output, frameBranchCall = .ok output ∧ output.code = #[.jump 0] ∧
      (output.state.alias[192]?).join = some 193) := by
  cases call : frameBranchCall with
  | error e => have success := frameBranch_success; simp only [call, Except.isOk] at success; cases success
  | ok output =>
    have observation := frameBranch_observed
    simp only [call, Except.toOption, Option.map_some, Option.some.injEq] at observation
    refine ⟨output, rfl, observation, ?_⟩
    have payloads : ∀ r ∈ frameBranchCtx.tryRegs.2, ∀ c, r ≠ .vreg 192 c := by
      intro r member c
      change r ∈ ([] : List Reg) at member
      cases member
    have actual : emitBranch frameBranchCtx frameFunction frameBlock.term 1 2 #[0] frameInput = .ok output := call
    have preserved := stock_emitBranch_aliasEntry (ctx := frameBranchCtx) (f := frameFunction)
      (t := frameBlock.term) (bi := 1) (ti := 2) (targets := #[0]) (input := frameInput)
      (output := output) (key := 192) payloads actual
    have entry : (frameInput.alias[192]?).join = some 193 := by decide
    exact preserved.trans entry

end Backend.Stock.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Assembly and recording do not undo the other-block alias frame. -/
theorem stock_lowerNode_other_aliasEntry {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    (ssa : (valueDefs f).Nodup) {x key owner ownerBlock bi label : Nat} {info : IInfo}
    (definition : ctx.insts[owner]? = some info) (result : x ∈ info.results)
    (mapped : ctx.valueReg? x = some (.vreg key .int))
    {first second : Clif.Block} (left : f.blocks[ownerBlock]? = some first)
    (right : f.blocks[bi]? = some second) (distinct : ownerBlock ≠ bi)
    {owned : Nat × Nat} {start stop : Nat}
    (firstRange : ranges[ownerBlock]? = some owned)
    (secondRange : ranges[bi]? = some (start, stop))
    (ownerLower : owned.1 ≤ owner) (ownerUpper : owner < owned.2)
    {order : Order} {paramBytes : List Nat} {input output : DriverState}
    (node : order.nodes[label]! = .original bi)
    (reservations : input.state.tryRegs = initial.tryRegs)
    (run : lowerNode ctx ranges order f paramBytes label input = .ok output) :
    (output.state.alias[key]?).join = (input.state.alias[key]?).join := by
  have block : f.blocks[bi]! = second := by simp only [getElem!_def, right]
  have range : ranges[bi]! = (start, stop) := by simp only [getElem!_def, secondRange]
  let fetchData : Except String V := match second.term with
    | .tryCall .. | .tryCallIndirect .. => tryCallData f second.term
    | _ => termData (abiTerm f second.term)
  let reject : Bool := (match second.term with | .ret .. => true | _ => false) &&
    (sretRet f).isEmpty && (sigRets f.sig != f.sig.returns)
  have normal : lowerNode ctx ranges order f paramBytes label input = (do
      let data ← fetchData
      if reject then throw "sret parameter is not an entry-block parameter"
      let lowered ← lowerBlockCore ctx order f second bi start stop data order.successors[label]! input.state
      let assembled ← assembleOriginalBlock ctx f second bi label order.successors[label]!
        lowered.outgoing paramBytes lowered.state.uses lowered.code
      pure { recordCore input lowered bi stop with
        blocks := input.blocks.set! label assembled,
        edgeArgs := input.edgeArgs.set! label lowered.outgoing }) := by
    unfold lowerNode
    simp only [node]
    rw [block, range]
    dsimp only [fetchData, reject]
    split <;> simp_all only [reject] <;> rfl
  rw [normal] at run
  cases dataRun : fetchData with
  | error e => simp only [dataRun, bind, Except.bind] at run; cases run
  | ok data =>
    simp only [dataRun, bind, Except.bind] at run
    split at run
    · cases run
    · cases core : lowerBlockCore ctx order f second bi start stop data order.successors[label]! input.state with
      | error e => simp only [core] at run; cases run
      | ok lowered =>
        simp only [core] at run
        cases assembled : assembleOriginalBlock ctx f second bi label order.successors[label]!
          lowered.outgoing paramBytes lowered.state.uses lowered.code with
        | error e => simp only [assembled] at run; cases run
        | ok block =>
          simp only [assembled, pure, Except.pure] at run
          cases run
          exact stock_lowerBlockCore_other_aliasEntry build ssa definition result mapped
            left right distinct firstRange secondRange ownerLower ownerUpper reservations core

end Backend.Stock.Proof

namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
private def nodeInput : DriverState := {
  state := frameInput
  blocks := Array.replicate 2 default
  edgeArgs := Array.replicate 2 #[]
  schedule := #[]
  scans := #[]
  blockScans := #[]
  rules := #[] }
private def nodeCall := lowerNode frameBuilt.1 frameBuilt.2.1 frameOrder frameFunction [] 1 nodeInput
private theorem node_success : nodeCall.isOk = true := by decide +kernel
private theorem node_observed : nodeCall.toOption.map
    (fun out => (out.blocks[1]!.insts, out.blockScans.size)) = some (#[.jump 0], 1) := by
  decide +kernel
private theorem node_built : Stock.buildCtx frameFunction = .ok frameBuilt := rfl
private theorem node_ssa : (valueDefs frameFunction).Nodup := by decide
private theorem node_definition : frameBuilt.1.insts[0]? =
    some (infoOf frameFunction ⟨[0], .iconst .i64 9⟩) := rfl
private theorem node_result : (0 : Nat) ∈ (infoOf frameFunction ⟨[0], .iconst .i64 9⟩).results := by decide
private theorem node_mapping : frameBuilt.1.valueReg? 0 = some (.vreg 192 .int) := rfl

/-- Actual node lowering assembles the jump and records its complete scan while
preserving an alias for a different source block's definition. Incoming state is chosen. -/
theorem stock_lowerNode_other_aliasEntry_witness :
    Stock.buildCtx frameFunction = .ok frameBuilt ∧
    (valueDefs frameFunction).Nodup ∧
    (∃ output, nodeCall = .ok output ∧ output.blocks[1]!.insts = #[.jump 0] ∧
      output.blockScans.size = 1 ∧ (output.state.alias[192]?).join = some 193) := by
  refine ⟨node_built, node_ssa, ?_⟩
  cases call : nodeCall with
  | error e => have success := node_success; simp only [call, Except.isOk] at success; cases success
  | ok output =>
    have observation := node_observed
    simp only [call, Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at observation
    refine ⟨output, rfl, observation.1, observation.2, ?_⟩
    have actual : lowerNode frameBuilt.1 frameBuilt.2.1 frameOrder frameFunction [] 1 nodeInput = .ok output := call
    have preserved := stock_lowerNode_other_aliasEntry
      (ctx := frameBuilt.1) (ranges := frameBuilt.2.1) (initial := frameBuilt.2.2)
      (start := 2) (stop := 3) (order := frameOrder) (paramBytes := [])
      (label := 1) (input := nodeInput) (output := output) node_built node_ssa
      (owner := 0) (ownerBlock := 0) (bi := 1) node_definition node_result node_mapping
      (first := frameFunction.blocks[0]!) (second := frameBlock) rfl rfl (by decide)
      (owned := (0, 2)) rfl rfl (by decide) (by decide) rfl rfl actual
    have entry : (nodeInput.state.alias[192]?).join = some 193 := by decide
    exact preserved.trans entry

end Backend.Stock.Proof
