import FV.Backend.Proof.StockBranchClassContracts
import FV.Backend.Proof.StockAliasClassInputs
import FV.Backend.Proof.StockCoverageBlock
namespace Backend.Stock.Proof.CoreClassDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.ClassGrowthDraft Backend.Stock.Proof.OperandClassDraft Backend.Stock.Proof.ScanClassDraft Backend.Stock.Proof.BranchClassDraft Backend.Stock.Proof.Coverage
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm scanBlock emitBranch lowerBlockCore branchArgs collectOutgoing
private def fields (st : State) := (st.base.classes, st.base.nextVreg)
private theorem fields_growth {st next : State} (h : fields next = fields st) :
    ClassGrowth st next := clsStep_of_eq (congrArg Prod.fst h) (congrArg Prod.snd h)
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
    fields b.1 = fields a.1 := by
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
    fields next = fields st := by
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
          exact forIn_frame (fun a : State × Array Reg => fields a.1) _
            (arg_frame ctx reservations.1 reservations.2 index nh)
            (arg_no_break ctx reservations.1 reservations.2 index nh) values loop
    · cases h
  · cases h

private theorem outgoing_frame {ctx : Ctx} {order : Order} {bi : Nat} {targets : Array Nat}
    {st next : State} {outgoing : Array (Array Reg)}
    (h : collectOutgoing ctx order bi targets st = .ok (next, outgoing)) :
    fields next = fields st := by
  unfold collectOutgoing at h
  apply fold_fields_eq (fun a : State × Array (Array Reg) => fields a.1) _ ?_ _ h
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



private theorem clean_stock {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) : Clean (sourceIdentityCtx ctx) := by
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  intro i info lookup
  change ctx.insts[i]? = some info at lookup
  rw [view.insts] at lookup
  exact Cov.clean_of_build legacy i info lookup

private theorem clean_block {f : Clif.Function} {ctx : Ctx}
    (clean : Clean (sourceIdentityCtx ctx)) {t : Clif.Terminator} {data : V}
    (prepared : blockData f t = .ok data) (ti : Nat) (trs : List Reg × List Reg) :
    Clean (sourceIdentityCtx {Driver.termCtx ctx ti data with tryRegs := trs}) := by
  cases t <;> simp only [blockData] at prepared
  all_goals first | exact clean_tryCtx clean prepared ti trs | exact clean_termCtx clean prepared ti

private theorem self_growth {ctx : Ctx} {before after : State}
    (growth : ClassGrowth before after) (initial : ClsIs ctx before.base before.base) :
    ClsIs ctx after.base after.base :=
  ⟨sz_step growth initial.sz,fun x r found => regCls_step growth (initial.vals x r found),
    fun r member => regCls_step growth (initial.try1 r member),
    fun r member => regCls_step growth (initial.try2 r member),⟨[],by simp,by simp⟩⟩

/-- Actual built original cores derive branch and complete body operand classes.
Prefix growth and unchanged reservations are internal traversal invariants. -/
theorem stock_built_core_classes {f : Clif.Function} {ctx : Ctx} {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) (scope : LowerScope f)
    {order : Order} {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range) {data : V}
    (prepared : blockData f b.term = .ok data) {targets : Array Nat} {input : State}
    (growth : ClassGrowth initial input) (tables : input.tryRegs = initial.tryRegs)
    {output : LoweredBlockCore}
    (run : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = .ok output) :
    ClassGrowth input output.state ∧
      ∀ i ∈ output.code.toList,RegsFrom (RegCls output.state.base.classes) i ∧ InstCls output.state.base.classes i := by
  let ti := range.2 - 1
  let selected : Ctx := {Driver.termCtx ctx ti data with tryRegs := input.tryRegs[ti]!}
  obtain ⟨original,before,legacy,spec,view⟩ := buildCtx_source build
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  have endEq : ti = blockStart f bi + b.body.length := by cases rangeEq; dsimp [ti] <;> omega
  have ph : ctx.insts[ti]? = some ⟨.op .unit,[],[],none⟩ := by
    rw [view.insts,endEq]
    exact spec.facts.term bi b block
  have mapped : MappedCtxInv f selected := ((buildCtx_mappedInv scope build).termCtx ph data).withTryRegs _
  have clean : Clean (sourceIdentityCtx selected) := clean_block (clean_stock build) prepared ti _
  have initialSelected : ClsIs selected initial.base initial.base := by
    dsimp only [selected]
    rw [tables]
    exact stock_build_term_classInvariant build ti data
  have inputClasses : ClsIs selected input.base input.base := self_growth growth initialSelected
  let branchCall : Except String (Option BranchEmission) :=
    if blockBranch b.term then some <$> emitBranch selected f b.term bi ti targets input else pure none
  have branchKeeps {br : Option BranchEmission} (call : branchCall = .ok br) :
      ClassGrowth input (br.map (fun e => e.state) |>.getD input) ∧
      ClsIs selected (br.map (fun e => e.state) |>.getD input).base (br.map (fun e => e.state) |>.getD input).base ∧
      ∀ i ∈ (br.map (fun e => e.code) |>.getD #[]).toList,
        RegsFrom (RegCls (br.map (fun e => e.state) |>.getD input).base.classes) i := by
    unfold branchCall at call
    split at call
    · cases emitted : emitBranch selected f b.term bi ti targets input with
      | error e => simp only [emitted,Functor.map,Except.map] at call; cases call
      | ok e =>
        simp only [emitted,Functor.map,Except.map] at call
        cases call
        have actual := stock_emitBranch_classes (ctx := selected) clean inputClasses emitted
        exact ⟨actual.1,actual.2.1,fun i member => (actual.2.2 i member).1⟩
    · cases call
      exact ⟨clsStep_refl _,inputClasses,by simp⟩
  have normal : lowerBlockCore ctx order f b bi range.1 range.2 data targets input = ((do
    let br ← branchCall
    let edge ← collectOutgoing ctx order bi targets (br.map (fun e => e.state) |>.getD input)
    let next := edge.1
    let outgoing := edge.2
    let beforeScan := {next with color := some next.endColor[bi]!}
    let indices := ((Array.range (range.2-range.1)).map (range.1+·)).reverse.toList
    let body ← scanBlock selected bi ti (blockBranch b.term) indices beforeScan
    pure ⟨body.state,body.code ++ (br.map (fun e => e.code) |>.getD #[]),outgoing,br,
      ⟨selected,bi,ti,blockBranch b.term,indices,beforeScan,body⟩⟩) : Except String LoweredBlockCore) := by
    unfold lowerBlockCore
    dsimp only [branchCall,blockBranch,selected,ti]
    split <;> simp_all only [branchCall,blockBranch,selected,ti] <;> rfl
  rw [normal] at run
  cases call : branchCall with
  | error e => simp only [call,bind,Except.bind] at run; cases run
  | ok br =>
    simp only [call,bind,Except.bind] at run
    cases edges : collectOutgoing ctx order bi targets (br.map (fun e => e.state) |>.getD input) with
    | error e => simp only [edges,bind,Except.bind] at run; cases run
    | ok pair =>
      rcases pair with ⟨next,outgoing⟩
      simp only [edges,bind,Except.bind] at run
      let beforeScan : State := {next with color := some next.endColor[bi]!}
      let indices := ((Array.range (range.2-range.1)).map (range.1+·)).reverse.toList
      have branchFacts := branchKeeps call
      have framed : fields beforeScan = fields (br.map (fun e => e.state) |>.getD input) := by
        change fields next = fields (br.map (fun e => e.state) |>.getD input)
        exact outgoing_frame edges
      have edgeGrowth : ClassGrowth (br.map (fun e => e.state) |>.getD input) beforeScan :=
        fields_growth framed
      have beforeClasses := self_growth edgeGrowth branchFacts.2.1
      cases bodyRun : scanBlock selected bi ti (blockBranch b.term)
          ((Array.range (range.2-range.1)).map (range.1+·)).reverse.toList
          {next with color := some next.endColor[bi]!} with
      | error e => simp only [bodyRun,bind,Except.bind] at run; cases run
      | ok body =>
        simp only [bodyRun,bind,Except.bind,pure,Except.pure] at run
        cases run
        have slots := Coverage.built_scan_slots build scope block rangeRun prepared input.tryRegs[ti]!
        have bodyFacts := stock_scanBlock_classes mapped clean slots beforeClasses bodyRun
        have suffixGrowth := clsStep_trans edgeGrowth bodyFacts.1
        refine ⟨clsStep_trans branchFacts.1 suffixGrowth,?_⟩
        intro i member
        have either : i ∈ body.code.toList ∨ i ∈ (br.map (fun e => e.code) |>.getD #[]).toList := by
          simpa only [Array.toList_append,List.mem_append] using member
        rcases either with inBody | inBranch
        · exact bodyFacts.2.2.1 i inBody
        · have raw := (branchFacts.2.2 i inBranch).mono (fun r h => regCls_step suffixGrowth h)
          exact ⟨raw,instCls_of raw⟩
end Backend.Stock.Proof.CoreClassDraft
