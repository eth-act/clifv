import FV.Backend.Proof.StockTerminalFormContracts

namespace Backend.Stock.Proof.Coverage.CoreDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Cov Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.Coverage.TerminalDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm emitInstruction

private theorem branchCode_covered {f : Clif.Function} {t : Clif.Terminator} {targets : Array Nat}
    {input output : Array MInst} (covered : ∀ i ∈ input.toList,Covered i = true)
    (run : branchCode f t targets input = .ok output) :
    ∀ i ∈ output.toList,Covered i = true := by
  unfold branchCode at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals
    cases run
    first
      | exact covered
      | (intro i member
         simp only [Array.toList_push,List.mem_append,List.mem_singleton] at member
         rcases member with old | rfl
         · exact covered i (List.dropLast_subset _ (by simpa only [Array.toList_pop] using old))
         · rfl)

/-- Actual branch emission, including the final call-to-TryCall rewrite,
preserves covered forms and ordinary spill-static facts. -/
theorem stock_emitBranch_form_coverage {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {t : Clif.Terminator} {bi ti : Nat} {targets : Array Nat}
    {input : State} {output : BranchEmission}
    (run : emitBranch ctx f t bi ti targets input = .ok output) :
    ∀ i ∈ output.code.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
  unfold emitBranch at run
  dsimp only at run
  let before : State := {input with current := some ti,color := none,base.emitted := #[]}
  change ((do
    let (out,next,fired) ← Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before
    if out.isNone then throw s!"no lowering rule for terminator {repr t}"
    let code ← branchCode f t targets next.base.emitted
    pure ⟨next,code,⟨bi,ti,.emitted,before,next,[],fired,code⟩,fired⟩) :
      Except String BranchEmission) = .ok output at run
  cases root : Stock.runTerm ctx "lower_branch" [.inst ti,.labels targets.toList] before with
  | error e => simp only [root,bind,Except.bind] at run; cases run
  | ok answer =>
    rcases answer with ⟨out,next,fired⟩
    simp only [root,bind,Except.bind] at run
    split at run
    · cases run
    · cases call : branchCode f t targets next.base.emitted with
      | error e => simp only [call] at run; cases run
      | ok code =>
        simp only [call,pure,Except.pure] at run
        cases run
        obtain ⟨fragment,emitted,covered⟩ := Emission.stock_branch_emission_coverage mapped clean root
        have original : ∀ i ∈ next.base.emitted.toList,Covered i = true := by
          rw [emitted]
          simpa only [before,Array.empty_append,List.toList_toArray] using covered
        have forms := branchCode_covered original call
        intro i member
        have form := forms i member
        refine ⟨form,fun ordinary => spillInstOk_of_formOk (ctx := default) ?_⟩
        simpa only [Covered,ordinary,Bool.false_or] using form

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

theorem stock_blockCore_form_coverage {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range)
    {data : V} (prepared : blockData f b.term = .ok data)
    {order : Order} {targets : Array Nat} {input : State} {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = .ok output) :
    ∀ i ∈ output.code.toList,Covered i = true ∧ (i.isCtl = false → SpillInstOk i) := by
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
      ∀ i ∈ (br.map (fun e => e.code) |>.getD #[]).toList,Covered i = true := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch termCtx f b.term bi ti targets input with
      | error e => simp only [emitted,Functor.map,Except.map] at call; cases call
      | ok e =>
        simp only [emitted,Functor.map,Except.map] at call
        cases call
        intro i member
        exact (stock_emitBranch_form_coverage mapped clean emitted i member).1
    · cases call; intro i member; cases member
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
      let beforeScan : State := {next with color := some next.endColor[bi]!}
      let indices := ((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList
      change (scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan >>= fun bodyScan =>
        pure (⟨bodyScan.state, bodyScan.code ++ (br.map (fun (e : BranchEmission) => e.code) |>.getD #[]), outgoing,
          br, ⟨termCtx, bi, ti, blockBranch b.term, indices, beforeScan, bodyScan⟩⟩ : LoweredBlockCore)) =
            .ok output at run
      cases scan : scanBlock termCtx bi ti (blockBranch b.term) indices beforeScan with
      | error e => simp only [scan, bind, Except.bind] at run; cases run
      | ok body =>
        simp only [scan, bind, Except.bind, pure, Except.pure] at run
        cases run
        intro i member
        have either : i ∈ body.code.toList ∨ i ∈ (br.map (fun e => e.code) |>.getD #[]).toList := by
          simpa only [Array.toList_append,List.mem_append] using member
        rcases either with inBody | inBranch
        · exact stock_built_scanBlock_form_coverage build scope block rangeRun prepared _ scan i inBody
        · have form := branch_keeps call i inBranch
          refine ⟨form,fun ordinary => spillInstOk_of_formOk (ctx := default) ?_⟩
          simpa only [Covered,ordinary,Bool.false_or] using form


end Backend.Stock.Proof.Coverage.CoreDraft
