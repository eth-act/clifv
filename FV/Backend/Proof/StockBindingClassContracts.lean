import FV.Backend.Proof.StockClassRoots
import FV.Backend.Proof.StockClassGrowthContracts
import FV.Backend.Proof.StockBindingCoverage
import FV.Backend.Proof.StockBindingFlow

namespace Backend.Stock.Proof.BindingClassDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.Coverage.Result
open Backend.Stock.Proof.OperandClassDraft Backend.Stock.Proof.ClassGrowthDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm

/-- Each installed integer alias connects registers with their actual recorded
integer class; this is an internal state invariant, not a source input filter. -/
def AliasClasses (st : State) : Prop := ∀ (key target : Nat),
  (st.alias[key]?).join = some target →
    st.base.classes[key]? = some RegClass.int ∧ st.base.classes[target]? = some RegClass.int

/-- Actual ordered binding preserves alias class consistency. Repeated keys and
physical-result copies are allowed; every new alias comes from its actual output.
Output class facts are supplied by the real class analysis at emission. -/
theorem stock_bindResults_alias_classes {ctx : Ctx} {pairs : List (Nat × List Reg)} {before : State}
    (mapped : ∀ x r,ctx.valueReg? x = some r → ∃ n,r = .vreg n .int)
    (values : ∀ x r,ctx.valueReg? x = some r → RegCls before.base.classes r)
    (outputs : ∀ pair ∈ pairs,∀ r ∈ pair.2,RegCls before.base.classes r)
    (old : AliasClasses before) {after : State} {copies : Array MInst}
    (run : bindResults ctx pairs before = .ok (after,copies)) :
    after.base = before.base ∧ AliasClasses after := by
  obtain ⟨base,origins⟩ := stock_bindResults_aliasOrigins
    (fun key target => before.base.classes[key]? = some RegClass.int ∧ before.base.classes[target]? = some RegClass.int)
    mapped (by
      intro x rs member key target lookup result
      refine ⟨regCls_vreg.mp (values x (.vreg key .int) lookup),?_⟩
      have good := outputs (x,rs) member (.vreg target .int) (by rw [result]; simp)
      exact regCls_vreg.mp good) run
  refine ⟨base,fun key target entry => ?_⟩
  rw [base]
  rcases origins key target entry with previous | new
  · exact old key target previous
  · exact new

private theorem zip_right {α β : Type} {xs : List α} {ys : List β} {x : α} {y : β}
    (member : (x,y) ∈ xs.zip ys) : y ∈ ys := by
  obtain ⟨j,atPair⟩ := List.mem_iff_getElem?.mp member
  exact List.mem_of_getElem? (List.getElem?_zip_eq_some.mp atPair).2

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

/-- A class-consistent alias array makes the actual final resolver preserve
register classes and gives operand classes for the renamed instruction. -/
theorem stock_resolve_alias_classes {st : State} (aliases : AliasClasses st)
    (fuel : Nat) :
    (∀ r,RegCls st.base.classes r → RegCls st.base.classes (Backend.lowerFunction.resolve st.alias fuel r)) ∧
    (∀ i,RegsFrom (RegCls st.base.classes) i →
      InstCls st.base.classes (i.mapRegs (Backend.lowerFunction.resolve st.alias fuel))) := by
  have resolved := resolve_cls aliases fuel
  exact ⟨resolved,fun i held => instCls_mapRegs held resolved⟩

/-- Actual source emission and ordered binding supply operand classes, including
an empty result list, internally derived virtual outputs and zero binding copies. -/
theorem stock_emitInstruction_classes {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before : State} (invariant : ClsIs ctx before.base before.base) {emission : Emission} (empty : before.base.emitted = #[])
    (run : emitInstruction ctx ii before = .ok emission) :
    ClsIs ctx before.base emission.state.base ∧
      ∀ i ∈ emission.code.toList,RegsFrom (RegCls emission.state.base.classes) i ∧ InstCls emission.state.base.classes i := by
  unfold emitInstruction at run
  cases lowered : Stock.runTerm ctx "lower" [.inst ii] before with
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
      split at run
      · cases run
      · cases binding : bindResults ctx (ctx.insts[ii]!.results.zip rss) next with
        | error e => simp only [binding,bind,Except.bind] at run; cases run
        | ok answer =>
          rcases answer with ⟨bound,copies⟩
          simp only [binding,pure,Except.pure] at run
          cases run
          have atInfo : ctx.insts[ii]! = info := by rw [getElem!_def,source]
          rw [atInfo] at binding
          have virtual : ∀ pair ∈ info.results.zip rss,∀ r ∈ pair.2,∃ n,r = .vreg n .int := by
            intro pair member r inside
            by_cases none : info.results = []
            · simp [none] at member
            · exact stock_statement_result_registers mapped clean source original lowered none r (mem_regsVec (zip_right member) inside)
          obtain ⟨sameBase,noCopies⟩ := stock_bindResults_virtual_only mapped.valueReg virtual binding
          have classed := (stock_statement_classes mapped clean source original lowered invariant).1
          refine ⟨?_,?_⟩
          · change ClsIs ctx before.base bound.base
            rw [sameBase]; exact classed
          · obtain ⟨code,since,covered⟩ := classed.emitted
            intro i member
            dsimp only at member ⊢
            rw [sameBase,noCopies,Array.append_empty,since,empty,Array.empty_append] at member
            have inCode : i ∈ code := by simpa only [List.toList_toArray] using member
            rw [sameBase]
            exact ⟨covered i inCode,instCls_of (covered i inCode)⟩

/-- Every actual statement scan has class-consistent emitted instructions,
including sunk/omitted/skipped/committed empty-code decisions. Its state keeps
all mapped source/reserved classes and allocation size from the input. -/
theorem stock_scanInstruction_classes {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {block ii ti : Nat} {branch : Bool} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before : State} (invariant : ClsIs ctx before.base before.base) {scan : Scan}
    (run : scanInstruction ctx block ii ti branch before = .ok scan) :
    ClsIs ctx scan.state.base scan.state.base ∧
      ∀ i ∈ scan.emitted.toList,RegsFrom (RegCls scan.state.base.classes) i ∧ InstCls scan.state.base.classes i := by
  have growth := stock_scan_classGrowth run
  have final : ClsIs ctx scan.state.base scan.state.base :=
    ⟨sz_step growth invariant.sz,
      fun x r lookup => regCls_step growth (invariant.vals x r lookup),
      fun r member => regCls_step growth (invariant.try1 r member),
      fun r member => regCls_step growth (invariant.try2 r member),⟨[],by simp,by simp⟩⟩
  refine ⟨final,?_⟩
  unfold scanInstruction at run
  dsimp only at run
  repeat' first
    | (solve | cases run; intro i member; cases member)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  all_goals first
    | (solve | cases run)
    | (cases run
       exact (stock_emitInstruction_classes mapped clean source original (reset_classes ctx before ii invariant)
         (by unfold scanState; dsimp only; split <;> rfl) (by assumption)).2)

end Backend.Stock.Proof.BindingClassDraft
