import FV.Backend.Proof.StockBindingClassContracts
import FV.Backend.Proof.StockTerminalFormContracts
namespace Backend.Stock.Proof.ScanClassDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.OperandClassDraft Backend.Stock.Proof.ClassGrowthDraft
open Backend.Stock.Proof.Coverage Backend.Stock.Proof.Coverage.TerminalDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem reset_classes (ctx : Ctx) (st : State) (i : Nat)
    (input : ClsIs ctx st.base st.base) :
    ClsIs ctx (scanState st i).base (scanState st i).base := by
  have classes : (scanState st i).base.classes = st.base.classes := by
    unfold scanState; dsimp only; split <;> rfl
  have frontier : (scanState st i).base.nextVreg = st.base.nextVreg := by
    unfold scanState; dsimp only; split <;> rfl
  refine ⟨?_,?_,?_,?_,⟨[],by simp,by simp⟩⟩
  · simpa only [Sz,classes,frontier] using input.sz
  · intro x r lookup; change RegCls (scanState st i).base.classes r
    rw [classes]; exact input.vals x r lookup
  · intro r member; change RegCls (scanState st i).base.classes r
    rw [classes]; exact input.try1 r member
  · intro r member; change RegCls (scanState st i).base.classes r
    rw [classes]; exact input.try2 r member


private theorem self_growth {ctx : Ctx} {before after : State}
    (growth : ClassGrowth before after) (initial : ClsIs ctx before.base before.base) :
    ClsIs ctx after.base after.base :=
  ⟨sz_step growth initial.sz,fun x r found => regCls_step growth (initial.vals x r found),
    fun r member => regCls_step growth (initial.try1 r member),
    fun r member => regCls_step growth (initial.try2 r member),⟨[],by simp,by simp⟩⟩

/-- Actual return/trap emission derives operand classes through its root and
empty-result binding; no caller copy or instruction-class certificate is used. -/
theorem stock_emit_retTrap_classes {ctx : Ctx} (clean : Clean ctx)
    {ti : Nat} {t : Clif.Terminator} {data : V} (retTrap : retOrTrap t = true)
    (dataRun : Backend.termData t = .ok data) (slot : ctx.insts[ti]? = some ⟨data,[],[],none⟩)
    {before : State} (invariant : ClsIs ctx before.base before.base)
    {emission : Emission} (empty : before.base.emitted = #[])
    (run : emitInstruction ctx ti before = .ok emission) :
    ClsIs ctx before.base emission.state.base ∧
      ∀ i ∈ emission.code.toList,RegsFrom (RegCls emission.state.base.classes) i ∧ InstCls emission.state.base.classes i := by
  unfold emitInstruction at run
  have atInfo : ctx.insts[ti]! = ⟨data,[],[],none⟩ := by rw [getElem!_def,slot]
  cases lowered : Stock.runTerm ctx "lower" [.inst ti] before with
  | error e => simp only [lowered,bind,Except.bind] at run; cases run
  | ok answer =>
    rcases answer with ⟨out,next,trace⟩
    simp only [lowered,bind,Except.bind] at run
    cases out with
    | none => cases run
    | some out =>
      cases out <;> try (cases run)
      rename_i rss
      dsimp only at run
      rw [atInfo] at run
      simp only [List.isEmpty_nil,Bool.not_true,Bool.and_false,ite_false,List.zip_nil_left,
        bindResults,List.foldlM_nil,pure,Except.pure,bind,Except.bind] at run
      cases run
      have classes := stock_retTrap_classes clean retTrap dataRun slot lowered invariant
      refine ⟨classes,?_⟩
      obtain ⟨code,since,covered⟩ := classes.emitted
      intro i member
      dsimp only at member ⊢
      rw [Array.append_empty,since,empty,Array.empty_append] at member
      have raw := covered i (by simpa only [List.toList_toArray] using member)
      exact ⟨raw,instCls_of raw⟩

/-- Every real scan decision at a source or terminal slot yields operand-class
facts; skipped branch slots are empty and retain the same class invariants. -/
theorem stock_scan_slot_classes {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ii ti : Nat} {branch : Bool} (slot : ScanSlot ctx ii ti branch)
    {input : State} (invariant : ClsIs ctx input.base input.base) {output : Scan}
    (run : scanInstruction ctx block ii ti branch input = .ok output) :
    ClsIs ctx output.state.base output.state.base ∧
      ∀ i ∈ output.emitted.toList,RegsFrom (RegCls output.state.base.classes) i ∧ InstCls output.state.base.classes i := by
  have final := self_growth (stock_scan_classGrowth run) invariant
  rcases slot with ⟨info,inst,source,original⟩ | branchSlot | ⟨term,data,retTrap,prepared,source⟩
  · exact stock_scanInstruction_classes mapped clean source original invariant run
  · refine ⟨final,?_⟩
    obtain ⟨equal,isBranch⟩ := branchSlot
    subst ii
    subst branch
    by_cases sunk : input.sunk[ti]! = true
    · simp only [scanInstruction,sunk,ite_true] at run
      cases run; intro i member; cases member
    · simp only [scanInstruction,sunk,ite_false,beq_self_eq_true,Bool.true_and,ite_true] at run
      cases run; intro i member; cases member
  · refine ⟨final,?_⟩
    unfold scanInstruction at run
    dsimp only at run
    repeat' first
      | (solve | cases run; intro i member; cases member)
      | simp only [bind,Except.bind,pure,Except.pure] at run
      | split at run
    all_goals first
      | (solve | cases run)
      | (cases run
         exact (stock_emit_retTrap_classes (ctx := ctx) clean retTrap prepared source
           (reset_classes ctx input ii invariant)
           (by unfold scanState; dsimp only; split <;> rfl) (by assumption)).2)

/-- Complete real backward scans transport all earlier emitted instructions to
the final class table, while recording class invariants at every real endpoint.
All source/terminal decisions and class growth are composed internally. -/
theorem stock_scanBlock_classes {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ti : Nat} {branch : Bool} {indices : List Nat}
    (slots : ∀ i ∈ indices,ScanSlot ctx i ti branch)
    {input : State} (invariant : ClsIs ctx input.base input.base) {output : BlockScan}
    (run : scanBlock ctx block ti branch indices input = .ok output) :
    ClassGrowth input output.state ∧ ClsIs ctx output.state.base output.state.base ∧
      (∀ i ∈ output.code.toList,RegsFrom (RegCls output.state.base.classes) i ∧ InstCls output.state.base.classes i) ∧
      (∀ record ∈ output.records,ClsIs ctx record.input.base record.input.base ∧
        ClsIs ctx record.output.state.base record.output.state.base) := by
  have cert := runScans_spec run
  clear run
  induction cert with
  | nil input => exact ⟨clsStep_refl _,invariant,by simp,by simp⟩
  | @cons ii indices input scan tail head rest ih =>
    have first := stock_scan_slot_classes mapped clean (slots ii (List.mem_cons_self ..)) invariant head
    have last := ih (fun j member => slots j (List.mem_cons_of_mem ii member)) first.1
    refine ⟨clsStep_trans (stock_scan_classGrowth head) last.1,last.2.1,?_,?_⟩
    · intro i member
      have either : i ∈ tail.code.toList ∨ i ∈ scan.emitted.toList := by
        simpa only [Array.toList_append,List.mem_append] using member
      rcases either with left | right
      · exact last.2.2.1 i left
      · have classed := (first.2 i right).1.mono (fun r h => regCls_step last.1 h)
        exact ⟨classed,instCls_of classed⟩
    · intro record member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨invariant,first.1⟩
      · exact last.2.2.2 record member
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


/-- Real source build/scope/block/range and term data derive all mapped, clean
and scan-slot facts; only the internal entry class invariant is threaded. -/
theorem stock_built_scanBlock_classes {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx, ranges, initial)) (scope : LowerScope f)
    {bi : Nat} {b : Clif.Block} (block : f.blocks[bi]? = some b)
    {range : Nat × Nat} (rangeRun : ranges[bi]? = some range)
    {data : V} (prepared : blockData f b.term = .ok data) (trs : List Reg × List Reg)
    {input : State} {output : BlockScan}
    (invariant : ClsIs {Driver.termCtx ctx (range.2 - 1) data with tryRegs := trs} input.base input.base)
    (run : scanBlock {Driver.termCtx ctx (range.2 - 1) data with tryRegs := trs}
      bi (range.2 - 1) (blockBranch b.term)
      (((Array.range (range.2 - range.1)).map (range.1 + ·)).reverse.toList) input = .ok output) :
    ClassGrowth input output.state ∧
      ClsIs {Driver.termCtx ctx (range.2 - 1) data with tryRegs := trs} output.state.base output.state.base ∧
      (∀ i ∈ output.code.toList,RegsFrom (RegCls output.state.base.classes) i ∧ InstCls output.state.base.classes i) ∧
      (∀ record ∈ output.records,ClsIs {Driver.termCtx ctx (range.2 - 1) data with tryRegs := trs} record.input.base record.input.base ∧
        ClsIs {Driver.termCtx ctx (range.2 - 1) data with tryRegs := trs} record.output.state.base record.output.state.base) := by
  obtain ⟨original, before, legacy, spec, view⟩ := buildCtx_source build
  have rangeEq := spec.ranges bi b block
  rw [rangeRun] at rangeEq
  have endEq : range.2 - 1 = blockStart f bi + b.body.length := by cases rangeEq; omega
  have ph : ctx.insts[range.2 - 1]? = some ⟨.op .unit, [], [], none⟩ := by
    rw [endEq]
    exact placeholder build block
  have mapped := ((buildCtx_mappedInv scope build).termCtx ph data).withTryRegs trs
  exact stock_scanBlock_classes mapped (clean_block (clean_stock build) prepared _ trs)
    (built_scan_slots build scope block rangeRun prepared trs) invariant run





end Backend.Stock.Proof.ScanClassDraft
