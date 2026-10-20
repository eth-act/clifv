import FV.Backend.Proof.StockAliasClassInputs
import FV.Backend.Proof.StockScanClassContracts
namespace Backend.Stock.Proof.EmissionAliasClassDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.Cov Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.HelperAliasClassDraft Backend.Stock.Proof.OperandClassDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm
private theorem zip_right {α β : Type} {xs : List α} {ys : List β} {x : α} {y : β}
    (member : (x,y) ∈ xs.zip ys) : y ∈ ys := by
  obtain ⟨j,atPair⟩ := List.mem_iff_getElem?.mp member
  exact List.mem_of_getElem? (List.getElem?_zip_eq_some.mp atPair).2


/-- Actual statement selection and ordered binding preserve alias/reservation
classes using the real result-class analysis, without a post-root certificate. -/
theorem stock_emitInstruction_alias_classes {f : Clif.Function} {ctx : Ctx}
    (mapped : MappedCtxInv f ctx) (clean : Clean (sourceIdentityCtx ctx))
    {ii : Nat} {info : IInfo} {inst : Clif.Inst}
    (source : ctx.insts[ii]? = some info) (original : info.clif = some inst)
    {before : State} (invariant : ClsIs ctx before.base before.base) (reserved : ReservedClasses ctx before) (old : AliasClasses before) {emission : Emission}
    (run : emitInstruction ctx ii before = .ok emission) :
    AliasClasses emission.state ∧ ReservedClasses ctx emission.state := by
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
          have classed := stock_statement_classes mapped clean source original lowered invariant
          obtain ⟨rootAliases,rootReserved⟩ := stock_named_alias_classes reserved old lowered
          have outputs : ∀ pair ∈ info.results.zip rss,∀ r ∈ pair.2,RegCls next.base.classes r := by
            intro pair member r inside
            by_cases none : info.results = []
            · simp [none] at member
            · exact classed.2 _ rfl none r (mem_regsVec (zip_right member) inside)
          obtain ⟨base,aliases⟩ := stock_bindResults_alias_classes mapped.valueReg classed.1.vals outputs rootAliases binding
          refine ⟨aliases,?_⟩
          intro r member
          change IntCls bound.base.classes r
          rw [base]
          exact rootReserved r member

/-- Actual return/trap emission binds no source results, so helper preservation
supplies alias classes and reservation classes for the complete emission. -/
theorem stock_emit_empty_results_alias_classes {ctx : Ctx} {ii : Nat} {info : IInfo}
    (slot : ctx.insts[ii]? = some info) (empty : info.results = [])
    {before : State} (reserved : ReservedClasses ctx before) (old : AliasClasses before)
    {emission : Emission} (run : emitInstruction ctx ii before = .ok emission) :
    AliasClasses emission.state ∧ ReservedClasses ctx emission.state := by
  unfold emitInstruction at run
  have atInfo : ctx.insts[ii]! = info := by rw [getElem!_def,slot]
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
      rw [atInfo,empty] at run
      simp only [List.isEmpty_nil,Bool.not_true,Bool.and_false,ite_false,List.zip_nil_left,
        bindResults,List.foldlM_nil,pure,Except.pure,bind,Except.bind] at run
      cases run
      exact stock_named_alias_classes reserved old lowered

end Backend.Stock.Proof.EmissionAliasClassDraft
