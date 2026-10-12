import FV.Backend.Proof.StockCoverageScans
import FV.Backend.Proof.StockBlockRanges

/-! Derive scan metadata from actual context construction and source block ranges.
These are internal facts of the existing driver, not accepted-input certificates. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

section Preservation
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction emitBranch

/-- The actual block-core branch decision. -/
def blockBranch : Clif.Terminator → Bool
  | .ret .. | .trap .. | .returnCall .. => false
  | _ => true

/-- The actual node's terminator-data preparation, including exception calls. -/
def blockData (f : Clif.Function) (t : Clif.Terminator) : Except String V :=
  match t with
  | .tryCall .. | .tryCallIndirect .. => Backend.tryCallData f t
  | _ => Backend.termData (abiTerm f t)

private theorem termE {f : Clif.Function} (scope : LowerScope f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) : Compile.termE b.term = true := by
  have subset := scope.subsetE
  simp only [Compile.functionE, Bool.and_eq_true, List.all_eq_true] at subset
  exact (subset.2 b (List.mem_of_getElem? block)).2

private theorem placeholder {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) :
    ctx.insts[blockStart f bi + b.body.length]? = some ⟨.op .unit, [], [], none⟩ := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  rw [view.insts]
  exact spec.facts.term bi b block

private theorem term_slot {f : Clif.Function} (scope : LowerScope f)
    {ctx : Ctx} {i : Nat} {b : Clif.Block} {bi : Nat}
    (block : f.blocks[bi]? = some b) {data : V} (prepared : blockData f b.term = .ok data)
    (slot : ctx.insts[i]? = some ⟨data, [], [], none⟩) :
    ScanSlot ctx i i (blockBranch b.term) := by
  have supported := termE scope block
  cases term : b.term <;>
    simp only [blockBranch, blockData, term] at prepared ⊢
  all_goals first
    | exact .inr (.inl ⟨rfl, rfl⟩)
    | (refine .inr (.inr ⟨abiTerm f _, data, ?_, prepared, slot⟩); rfl)
    | (simp [term, Compile.termE] at supported)

/-- Actual successful context/range/data construction supplies every slot
premise of the complete backward-scan theorem, including try-call branch slots. -/
theorem built_scan_slots {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range)
    {data : V} (prepared : blockData f b.term = .ok data) (trs : List Reg × List Reg) :
    ∀ i ∈ (((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList),
      ScanSlot {Driver.termCtx ctx (range.2 - 1) data with tryRegs := trs}
        i (range.2 - 1) (blockBranch b.term) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  cases rangeEq
  have ti : blockStart f bi + b.body.length + 1 - 1 = blockStart f bi + b.body.length := by omega
  rw [ti]
  intro i member
  obtain ⟨lo, hi⟩ := stock_backward_indices_mem member
  by_cases terminal : i = blockStart f bi + b.body.length
  · subst i
    exact term_slot scope block prepared (termCtx_insts_self (placeholder build block) data)
  · have index : i - blockStart f bi < b.body.length := by omega
    cases statement : b.body[i - blockStart f bi]? with
    | none => have outside := List.getElem?_eq_none_iff.mp statement; omega
    | some stm =>
      obtain ⟨info, lookup, clif, results⟩ := spec.facts.stmt bi b _ stm block statement
      have offset : blockStart f bi + (i - blockStart f bi) = i := by omega
      rw [offset] at lookup
      refine .inl ⟨info, stm.inst, ?_, clif⟩
      change (Driver.termCtx ctx (blockStart f bi + b.body.length) data).insts[i]? = some info
      rw [termCtx_insts_ne terminal, view.insts]
      exact lookup

private theorem clean_stock {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

private theorem clean_block {f : Clif.Function} {ctx : Ctx}
    (clean : Clean (sourceIdentityCtx ctx)) {t : Clif.Terminator} {data : V}
    (prepared : blockData f t = .ok data) (ti : Nat) (trs : List Reg × List Reg) :
    Clean (sourceIdentityCtx {Driver.termCtx ctx ti data with tryRegs := trs}) := by
  cases t <;> simp only [blockData] at prepared
  all_goals first
    | exact clean_tryCtx clean prepared ti trs
    | exact clean_termCtx clean prepared ti

/-- The real complete scan needs only actual build/scope/block/data facts;
its mapped context, clean patterns and slot metadata are derived internally. -/
theorem built_scanBlock_noOpportunity {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range)
    {data : V} (prepared : blockData f b.term = .ok data) (trs : List Reg × List Reg)
    {input : State} {output : BlockScan} (empty : NoOpportunity input)
    (run : scanBlock {Driver.termCtx ctx (range.2 - 1) data with tryRegs := trs}
      bi (range.2 - 1) (blockBranch b.term)
      (((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList) input = .ok output) :
    NoOpportunity output.state := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  have endEq : range.2 - 1 = blockStart f bi + b.body.length := by cases rangeEq; omega
  have ph : ctx.insts[range.2 - 1]? = some ⟨.op .unit, [], [], none⟩ := by
    rw [endEq]
    exact placeholder build block
  have mapped := ((buildCtx_mappedInv scope build).termCtx ph data).withTryRegs trs
  exact scanBlock_noOpportunity mapped (clean_block (clean_stock build) prepared _ trs)
    (built_scan_slots build scope block rangeRun prepared trs) empty run

private def frame (st : State) := st.opportunistic

private theorem forIn_frame {α β γ : Type} (field : α → γ)
    (step : β → α → Except String (ForInStep α))
    (keeps : ∀ x a b, step x a = .ok (.yield b) → field b = field a)
    (no_break : ∀ x a b, step x a ≠ .ok (.done b))
    (xs : List β) {a next : α} (h : forIn xs a step = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => simp only [List.forIn_nil, pure, Except.pure] at h; cases h; rfl
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases call : step x a with
    | error e => simp only [call, bind, Except.bind] at h; cases h
    | ok result =>
      cases result with
      | done b => exact False.elim (no_break x a b call)
      | yield b =>
        simp only [call, bind, Except.bind] at h
        exact (ih h).trans (keeps x a b call)

private def argStep (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (acc : State × Array Reg) :
    Except String (ForInStep (State × Array Reg)) := do
  match arg with
  | .val v =>
    let some r := ctx.valueReg? v | throw s!"unknown value v{v}"
    pure (.yield (acc.1.mark v, acc.2.push r))
  | .ret i =>
    if index < nh then throw "try_call return on exception edge"
    let some r := rets[i]? | throw "try_call return index"
    pure (.yield (acc.1, acc.2.push r))
  | .exn i =>
    if index == nh then throw "try_call payload on normal edge"
    let some r := pays[i]? | throw "try_call payload index"
    pure (.yield (acc.1, acc.2.push r))

private theorem arg_frame (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg)
    (h : argStep ctx rets pays index nh arg a = .ok (.yield b)) :
    frame b.1 = frame a.1 := by
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h <;> rfl) | split at h

private theorem arg_no_break (ctx : Ctx) (rets pays : List Reg) (index nh : Nat)
    (arg : Clif.TryArg) (a b : State × Array Reg) :
    argStep ctx rets pays index nh arg a ≠ .ok (.done b) := by
  intro h
  cases arg <;> unfold argStep at h
  all_goals repeat' first | (solve | cases h) | split at h

private theorem branch_frame {ctx : Ctx} {st next : State} {block index : Nat}
    {args : Array Reg} (h : branchArgs ctx st block index = .ok (args, next)) :
    frame next = frame st := by
  unfold branchArgs at h
  dsimp only at h
  split at h
  · rename_i id values lookup
    split at h
    · rename_i target found
      split at h
      · cases h
      · let ti := (st.instBlock.findIdx? (· == block)).getD 0 + ctx.func.blocks[block]!.body.length
        let reservations := st.tryRegs[ti]!
        let nh := match ctx.func.blocks[block]!.term with
          | .tryCall _ _ et | .tryCallIndirect _ _ et => et.handlers.length
          | _ => 0
        change (do
          let result ← forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh)
          pure (result.2, result.1)) = .ok (args, next) at h
        cases loop : forIn values (st, #[]) (argStep ctx reservations.1 reservations.2 index nh) with
        | error e => simp only [loop, bind, Except.bind] at h; cases h
        | ok result =>
          simp only [loop, bind, Except.bind, pure, Except.pure] at h
          cases h
          exact forIn_frame (fun a : State × Array Reg => frame a.1) _
            (arg_frame ctx reservations.1 reservations.2 index nh)
            (arg_no_break ctx reservations.1 reservations.2 index nh) values loop
    · cases h
  · cases h

/-- Actual successor argument collection may mark source demands, but retains
remembered definitions, including exception-return and payload arguments. -/
theorem branchArgs_noOpportunity {ctx : Ctx} {input next : State} {bi index : Nat}
    {args : Array Reg} (run : branchArgs ctx input bi index = .ok (args, next)) :
    next.opportunistic = input.opportunistic := branch_frame run

private theorem fold_fields_eq {α β γ : Type} (field : α → γ)
    (step : α → β → Except String α)
    (hs : ∀ a b next, step a b = .ok next → field next = field a)
    (xs : List β) {a next : α} (h : xs.foldlM step a = .ok next) :
    field next = field a := by
  induction xs generalizing a with
  | nil => cases h; rfl
  | cons x xs ih =>
    rw [List.foldlM_cons] at h
    cases he : step a x with
    | error e => simp only [he, bind, Except.bind] at h; cases h
    | ok middle =>
      simp only [he, bind, Except.bind] at h
      exact (ih h).trans (hs a x middle he)


private theorem outgoing_frame {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {outgoing : Array (Array Reg)}
    (h : collectOutgoing ctx order bi targets st = .ok (next, outgoing)) :
    frame next = frame st := by
  unfold collectOutgoing at h
  apply fold_fields_eq (fun a : State × Array (Array Reg) => frame a.1) _ ?_ _ h
  intro acc target result step
  unfold outgoingStep at step
  split at step
  · cases step; rfl
  · cases call : branchArgs ctx acc.1 bi target.2 with
    | error e => simp only [call, bind, Except.bind] at step; cases step
    | ok pair =>
      rcases pair with ⟨regs, state⟩
      simp only [call, bind, Except.bind, pure, Except.pure] at step
      cases step
      exact branch_frame call


private theorem branch_preserves {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {t : Clif.Terminator} {bi ti : Nat} {targets : Array Nat}
    {input : State} {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) :
    output.state.opportunistic = input.opportunistic := by
  unfold emitBranch at run
  dsimp only at run
  let before : State := {input with current := some ti, color := none, base.emitted := #[]}
  change ((do
    let (out, next, fired) ← Stock.runTerm ctx "lower_branch" [.inst ti, .labels targets.toList] before
    if out.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t targets next.base.emitted
    pure ⟨next, code, ⟨bi, ti, .emitted, before, next, [], fired, code⟩, fired⟩) :
      Except String BranchEmission) = .ok output at run
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
        exact branch_noOpportunity mapped clean (before := before) root

/-- All state-changing operations in an actual original block preserve empty
remembered definitions. Context and scan metadata are derived from its build. -/
theorem blockCore_noOpportunity {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range)
    {data : V} (prepared : blockData f b.term = .ok data)
    {order : Order} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (empty : NoOpportunity input)
    (run : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = .ok output) :
    NoOpportunity output.state := by
  let ti := range.2 - 1
  let termCtx : Ctx := {Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]!}
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  have endEq : ti = blockStart f bi + b.body.length := by cases rangeEq; simp [ti]
  have ph : ctx.insts[ti]? = some ⟨.op .unit, [], [], none⟩ := by
    rw [endEq]; exact placeholder build block
  have mapped : MappedCtxInv f termCtx :=
    ((buildCtx_mappedInv scope build).termCtx ph data).withTryRegs _
  have clean : Clean (sourceIdentityCtx termCtx) := clean_block (clean_stock build) prepared _ _
  let branchCall : Except String (Option BranchEmission) :=
    if blockBranch b.term then some <$> emitBranch termCtx f b.term bi ti targets input else pure none
  have branch_keeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      NoOpportunity (br.map (fun (e : BranchEmission) => e.state) |>.getD input) := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch termCtx f b.term bi ti targets input with
      | error e => simp only [emitted, Functor.map, Except.map] at call; cases call
      | ok e =>
        simp only [emitted, Functor.map, Except.map] at call
        cases call
        intro v
        change e.state.opportunistic[v]! = none
        rw [branch_preserves mapped clean emitted]
        exact empty v
    · cases call; exact empty
  have normal : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = ((do
    let br ← branchCall
    let edge ← collectOutgoing ctx order bi targets (br.map (fun (e : BranchEmission) => e.state) |>.getD input)
    let next := edge.1
    let outgoing := edge.2
    let beforeScan := {next with color := some next.endColor[bi]!}
    let indices := ((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList
    let bodyScan ← scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan
    pure ⟨bodyScan.state, bodyScan.code ++ (br.map (fun (e : BranchEmission) => e.code) |>.getD #[]), outgoing,
      br, ⟨termCtx, bi, ti, blockBranch b.term, indices, beforeScan, bodyScan⟩⟩) :
        Except String LoweredBlockCore) := by
    unfold lowerBlockCore
    dsimp only [branchCall, blockBranch, termCtx, ti]
    split <;> simp_all only [blockBranch, termCtx, ti] <;> rfl
  rw [normal] at run
  cases call : branchCall with
  | error e => simp only [call, bind, Except.bind] at run; cases run
  | ok br =>
    simp only [call, bind, Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (fun (e : BranchEmission) => e.state) |>.getD input) with
    | error e => simp only [edges] at run; cases run
    | ok result =>
      rcases result with ⟨next, outgoing⟩
      simp only [edges] at run
      have edgeEmpty : NoOpportunity next := by
        intro v
        rw [show next.opportunistic = (br.map (fun (e : BranchEmission) => e.state) |>.getD input).opportunistic from outgoing_frame edges]
        exact branch_keeps call v
      let beforeScan : State := {next with color := some next.endColor[bi]!}
      let indices := ((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList
      have beforeEmpty : NoOpportunity beforeScan := edgeEmpty
      change (scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan >>= fun bodyScan =>
        pure (⟨bodyScan.state, bodyScan.code ++ (br.map (fun (e : BranchEmission) => e.code) |>.getD #[]), outgoing,
          br, ⟨termCtx, bi, ti, blockBranch b.term, indices, beforeScan, bodyScan⟩⟩ : LoweredBlockCore)) =
            .ok output at run
      cases scan : scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan with
      | error e => simp only [scan, bind, Except.bind] at run; cases run
      | ok body =>
        simp only [scan, bind, Except.bind, pure, Except.pure] at run
        cases run
        exact built_scanBlock_noOpportunity build scope block rangeRun prepared _ beforeEmpty scan

end Preservation

private def blockFunction : Clif.Function := {
  name := "stock_block_preservation"
  sig := {callConv := some .systemV}
  blocks := [
    {id := 0, body := [⟨[2], .iconst .i8 9⟩], term := .jump ⟨1, []⟩},
    {id := 1, term := .ret []}] }
private def blockBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx blockFunction).toOption.getD (sinkCtx, #[], sinkState)
private def blockOrder : Order := {
  nodes := #[.original 0, .original 1]
  successors := #[#[1], #[]] }
private def blockTerm : Clif.Block := blockFunction.blocks[0]!
private def blockTermData : V := (blockData blockFunction blockTerm.term).toOption.getD (.op .unit)
private def blockCtx : Ctx :=
  {Driver.termCtx blockBuilt.1 1 blockTermData with tryRegs := blockBuilt.2.2.tryRegs[1]!}
private def branchBefore : State :=
  {blockBuilt.2.2 with current := some 1, color := none, base.emitted := #[]}
private def branchAfter : State := {branchBefore with base := branchBefore.base.emit (.jump 1)}
private def blockBranchOutput : BranchEmission :=
  ⟨branchAfter, #[.jump 1], ⟨0, 1, .emitted, branchBefore, branchAfter, [], [559, 6, 1139], #[.jump 1]⟩,
    [559, 6, 1139]⟩
private def blockScanBefore : State := {branchAfter with color := some branchAfter.endColor[0]!}
private def blockSkipped : State := scanState blockScanBefore 1
private def blockOmitted : State := scanState blockSkipped 0
private def blockScanOutput : BlockScan := ⟨blockOmitted,
  [⟨1, blockScanBefore, ⟨blockSkipped, none, #[]⟩⟩,
   ⟨0, blockSkipped, ⟨blockOmitted, some ⟨0, 0, .omitted, blockOmitted, blockOmitted, [], [], #[]⟩, #[]⟩⟩], #[]⟩
private def blockOutput : LoweredBlockCore :=
  ⟨blockOmitted, #[.jump 1], #[#[]], some blockBranchOutput,
    ⟨blockCtx, 0, 1, true, [1, 0], blockScanBefore, blockScanOutput⟩⟩
private theorem block_build : Stock.buildCtx blockFunction = .ok blockBuilt := rfl
private theorem block_scope : LowerScope blockFunction := lowerScope_of (by decide +kernel)
private theorem block_data : blockData blockFunction blockTerm.term = .ok blockTermData := rfl
private theorem block_branch_run : Stock.runTerm blockCtx "lower_branch" [.inst 1, .labels [1]] branchBefore =
    .ok (some (.op .unit), branchAfter, [559, 6, 1139]) := rfl
private theorem block_branch_emission : emitBranch blockCtx blockFunction blockTerm.term 0 1 #[1]
    blockBuilt.2.2 = .ok blockBranchOutput := by
  unfold emitBranch
  change ((do
    let (out, next, fired) ← Stock.runTerm blockCtx "lower_branch" [.inst 1, .labels [1]] branchBefore
    if out.isNone then throw s!"no lowering rule for terminator {repr blockTerm.term}"
    let code ← branchCode blockFunction blockTerm.term #[1] next.base.emitted
    pure ⟨next, code, ⟨0, 1, .emitted, branchBefore, next, [], fired, code⟩, fired⟩) :
      Except String BranchEmission) = .ok blockBranchOutput
  rw [block_branch_run]
  rfl
private theorem block_scan_run : scanBlock blockCtx 0 1 true [1, 0] blockScanBefore = .ok blockScanOutput := rfl
private theorem block_core_run : lowerBlockCore blockBuilt.1 blockOrder blockFunction blockTerm
    0 0 2 blockTermData #[1] blockBuilt.2.2 = .ok blockOutput := by
  have indices : (((Array.range (2 - 0)).map (0 + ·)).reverse.toList) = [1, 0] := by decide +kernel
  unfold lowerBlockCore
  dsimp only
  rw [indices]
  change (do
    let br : Option BranchEmission ← some <$> emitBranch blockCtx blockFunction blockTerm.term 0 1 #[1] blockBuilt.2.2
    let edge : State × Array (Array Reg) ← collectOutgoing blockBuilt.1 blockOrder 0 #[1] (br.map (fun (e : BranchEmission) => e.state) |>.getD blockBuilt.2.2)
    let scan : BlockScan ← scanBlock blockCtx 0 1 true [1, 0] {edge.1 with color := some edge.1.endColor[0]!}
    pure (⟨scan.state, scan.code ++ (br.map (fun (e : BranchEmission) => e.code) |>.getD #[]), edge.2,
      br, ⟨blockCtx, 0, 1, true, [1, 0], {edge.1 with color := some edge.1.endColor[0]!}, scan⟩⟩ :
        LoweredBlockCore)) = _
  rw [block_branch_emission]
  change (scanBlock blockCtx 0 1 true [1, 0] blockScanBefore >>= fun scan =>
    pure (⟨scan.state, scan.code ++ #[.jump 1], #[#[]], some blockBranchOutput,
      ⟨blockCtx, 0, 1, true, [1, 0], blockScanBefore, scan⟩⟩ : LoweredBlockCore)) = _
  rw [block_scan_run]
  rfl

/-- A real two-block build derives source and branch slot metadata without
supplying a per-slot certificate; the selected source interval contains a body. -/
theorem built_scan_slots_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State)
      (b : Clif.Block) (data : V),
      Stock.buildCtx f = .ok (ctx, ranges, initial) ∧ LowerScope f ∧
      f.blocks[0]? = some b ∧ b.body.length = 1 ∧ ranges[0]? = some (0, 2) ∧
      blockData f b.term = .ok data ∧
      (∀ i ∈ [1, 0], ScanSlot {Driver.termCtx ctx 1 data with tryRegs := initial.tryRegs[1]!} i 1
        (blockBranch b.term)) := by
  refine ⟨blockFunction, blockBuilt.1, blockBuilt.2.1, blockBuilt.2.2, blockTerm, blockTermData,
    block_build, block_scope, rfl, rfl, rfl, block_data,
    ?_⟩
  have slots := built_scan_slots (ctx := blockBuilt.1) (ranges := blockBuilt.2.1)
    (initial := blockBuilt.2.2) block_build block_scope (bi := 0) (b := blockTerm) rfl
    (range := (0, 2)) rfl block_data (blockBuilt.2.2.tryRegs[1]!)
  have indices : (((Array.range (2 - 0)).map (0 + ·)).reverse.toList) = [1, 0] := by decide +kernel
  rw [indices] at slots
  exact slots

/-- A real complete scan skips the already-emitted branch and omits the unused
constant; its build, source scope, range and data discharge all metadata facts. -/
theorem built_scanBlock_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial input : State)
      (b : Clif.Block) (data : V) (output : BlockScan),
      Stock.buildCtx f = .ok (ctx, ranges, initial) ∧ LowerScope f ∧
      f.blocks[0]? = some b ∧ ranges[0]? = some (0, 2) ∧ blockData f b.term = .ok data ∧
      NoOpportunity input ∧
      scanBlock {Driver.termCtx ctx 1 data with tryRegs := initial.tryRegs[1]!} 0 1
        (blockBranch b.term) [1, 0] input = .ok output ∧ output.records.length = 2 ∧
      NoOpportunity output.state := by
  have empty : NoOpportunity blockScanBefore := by
    intro v
    change blockBuilt.2.2.opportunistic[v]! = none
    exact buildCtx_noOpportunity block_build v
  refine ⟨blockFunction, blockBuilt.1, blockBuilt.2.1, blockBuilt.2.2, blockScanBefore,
    blockTerm, blockTermData, blockScanOutput, block_build, block_scope, rfl, rfl, block_data,
    empty, block_scan_run, rfl,
    ?_⟩
  have indices : (((Array.range (2 - 0)).map (0 + ·)).reverse.toList) = [1, 0] := by decide +kernel
  have run : scanBlock blockCtx 0 1 (blockBranch blockTerm.term)
      (((Array.range (2 - 0)).map (0 + ·)).reverse.toList) blockScanBefore = .ok blockScanOutput := by
    rw [indices]
    exact block_scan_run
  exact built_scanBlock_noOpportunity (ctx := blockBuilt.1) (ranges := blockBuilt.2.1)
    (initial := blockBuilt.2.2) block_build block_scope (bi := 0) (b := blockTerm) rfl
    (range := (0, 2)) rfl block_data (blockBuilt.2.2.tryRegs[1]!) empty run

/-- Actual branch emission, outgoing argument collection and a complete body
scan compose in a real nonempty block, retaining the emitted jump. -/
theorem blockCore_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial : State)
      (order : Order) (b : Clif.Block) (data : V) (output : LoweredBlockCore),
      Stock.buildCtx f = .ok (ctx, ranges, initial) ∧ LowerScope f ∧
      f.blocks[0]? = some b ∧ ranges[0]? = some (0, 2) ∧ blockData f b.term = .ok data ∧
      NoOpportunity initial ∧
      lowerBlockCore ctx order f b 0 0 2 data #[1] initial = .ok output ∧
      output.code = #[.jump 1] ∧ output.outgoing = #[#[]] ∧ output.scan.output.records.length = 2 ∧
      NoOpportunity output.state :=
  ⟨blockFunction, blockBuilt.1, blockBuilt.2.1, blockBuilt.2.2, blockOrder, blockTerm,
    blockTermData, blockOutput, block_build, block_scope, rfl, rfl, block_data,
    buildCtx_noOpportunity block_build, block_core_run, rfl, rfl, rfl,
    blockCore_noOpportunity block_build block_scope (bi := 0) rfl (range := (0, 2)) rfl block_data
      (buildCtx_noOpportunity block_build) block_core_run⟩

private def edgeFunction : Clif.Function := {
  name := "stock_edge_preservation"
  sig := {callConv := some .systemV}
  blocks := [
    {id := 0, body := [⟨[2], .iconst .i8 9⟩], term := .jump ⟨1, [2]⟩},
    {id := 1, params := [(5, .i8)], term := .ret []}] }
private def edgeBuilt : Ctx × Array (Nat × Nat) × State :=
  (Stock.buildCtx edgeFunction).toOption.getD (sinkCtx, #[], sinkState)
private theorem edge_build : Stock.buildCtx edgeFunction = .ok edgeBuilt := rfl
private theorem edge_run : branchArgs edgeBuilt.1 edgeBuilt.2.2 0 0 =
    .ok (#[.vreg 192 .int], edgeBuilt.2.2.mark 2) := rfl

/-- A real nonempty successor argument vector marks value2 demanded and retains
remembered definitions, inhabiting the frame used for critical-edge nodes. -/
theorem branchArgs_noOpportunity_witness :
    ∃ (f : Clif.Function) (ctx : Ctx) (ranges : Array (Nat × Nat)) (initial next : State),
      Stock.buildCtx f = .ok (ctx, ranges, initial) ∧
      branchArgs ctx initial 0 0 = .ok (#[.vreg 192 .int], next) ∧
      initial.demand[2]! = 0 ∧ next.demand[2]! = 1 ∧ next.opportunistic = initial.opportunistic :=
  ⟨edgeFunction, edgeBuilt.1, edgeBuilt.2.1, edgeBuilt.2.2, edgeBuilt.2.2.mark 2,
    edge_build, edge_run, rfl, rfl, branchArgs_noOpportunity edge_run⟩

end Backend.Stock.Proof.Coverage
