module

public import FV.Backend.Proof.StockTerminalScans
public import FV.Backend.Proof.StockCoverageBlock

@[expose] public section

/-! Actual block construction preserves unsunk source terminator placeholders,
including branch roots, exception arguments and all retained scan endpoints. -/
namespace Backend.Stock.Proof.Coverage
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitBranch scanBlock
private theorem term_clif {ctx : Ctx} {ti : Nat}
    (placeholder : ctx.insts[ti]? = some ⟨.op .unit,[],[],none⟩) (data : V) (j : Nat) :
    (Driver.termCtx ctx ti data).insts[j]!.clif = ctx.insts[j]!.clif := by
  by_cases same : j = ti
  · subst j
    simp only [getElem!_def,termCtx_insts_self placeholder data,placeholder,Option.getD_some]
  · simp only [getElem!_def,termCtx_insts_ne same]
private theorem safe_congr {ctx original : Ctx} {st : State}
    (same : ∀ j : Nat,ctx.insts[j]!.clif = original.insts[j]!.clif)
    (safe : TerminalUnsunk original st) : TerminalUnsunk ctx st := by
  intro j slot
  exact safe j ((same j).symm.trans slot)
private theorem placeholder {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial))
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b) :
    ctx.insts[blockStart f bi + b.body.length]? = some ⟨.op .unit, [], [], none⟩ := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  rw [view.insts]
  exact spec.facts.term bi b block

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

private def frame (st : State) := st.sunk

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
theorem stock_branchArgs_sunk {ctx : Ctx} {input next : State} {bi index : Nat}
    {args : Array Reg} (run : branchArgs ctx input bi index = .ok (args, next)) :
    next.sunk = input.sunk := branch_frame run

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
    (safe : TerminalUnsunk ctx input)
    (run : emitBranch ctx f t bi ti targets input = .ok output) :
    TerminalUnsunk ctx output.state := by
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
        intro terminal slot
        exact stock_branch_terminal_unsunk mapped clean (before := before) root slot (safe terminal slot)

theorem stock_blockCore_terminal_unsunk {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range)
    {data : V} (prepared : blockData f b.term = .ok data)
    {order : Order} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (empty : NoOpportunity input) (safe : TerminalUnsunk ctx input)
    (run : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = .ok output) :
    TerminalUnsunk ctx output.state ∧ TerminalUnsunk ctx output.scan.input ∧
      (∀ record ∈ output.scan.output.records,
        TerminalUnsunk ctx record.input ∧ TerminalUnsunk ctx record.output.state) := by
  have memories := blockCore_records_noOpportunity build scope block rangeRun prepared empty run
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
  have slotsSame : ∀ j : Nat,termCtx.insts[j]!.clif = ctx.insts[j]!.clif := by
    intro j
    exact term_clif ph data j
  have toTerm {s : State} (h : TerminalUnsunk ctx s) : TerminalUnsunk termCtx s := safe_congr slotsSame h
  have fromTerm {s : State} (h : TerminalUnsunk termCtx s) : TerminalUnsunk ctx s :=
    safe_congr (fun j => (slotsSame j).symm) h
  let branchCall : Except String (Option BranchEmission) :=
    if blockBranch b.term then some <$> emitBranch termCtx f b.term bi ti targets input else pure none
  have branch_keeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      TerminalUnsunk termCtx (br.map (fun (e : BranchEmission) => e.state) |>.getD input) := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch termCtx f b.term bi ti targets input with
      | error e => simp only [emitted, Functor.map, Except.map] at call; cases call
      | ok e =>
        simp only [emitted, Functor.map, Except.map] at call
        cases call
        exact branch_preserves mapped clean (toTerm safe) emitted
    · cases call; exact toTerm safe
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
      have edgeSafe : TerminalUnsunk termCtx next := by
        intro j slot
        change next.sunk[j]! = false
        rw [show next.sunk = (br.map (fun (e : BranchEmission) => e.state) |>.getD input).sunk from outgoing_frame edges]
        exact branch_keeps call j slot
      let beforeScan : State := {next with color := some next.endColor[bi]!}
      let indices := ((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList
      have beforeSafe : TerminalUnsunk termCtx beforeScan := edgeSafe
      change (scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan >>= fun bodyScan =>
        pure (⟨bodyScan.state, bodyScan.code ++ (br.map (fun (e : BranchEmission) => e.code) |>.getD #[]), outgoing,
          br, ⟨termCtx, bi, ti, blockBranch b.term, indices, beforeScan, bodyScan⟩⟩ : LoweredBlockCore)) =
            .ok output at run
      cases scan : scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan with
      | error e => simp only [scan, bind, Except.bind] at run; cases run
      | ok body =>
        simp only [scan, bind, Except.bind, pure, Except.pure] at run
        cases run
        have certificate := stock_scanBlock_terminal_unsunk mapped clean
          (built_scan_slots build scope block rangeRun prepared _) memories.1 beforeSafe scan
        exact ⟨fromTerm certificate.1,fromTerm beforeSafe,fun record member =>
          ⟨fromTerm (certificate.2 record member).1,fromTerm (certificate.2 record member).2⟩⟩

end Backend.Stock.Proof.Coverage
