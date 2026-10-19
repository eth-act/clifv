import FV.Backend.Proof.StockHelperAliasClasses
import FV.Backend.Proof.StockInitialClasses

namespace Backend.Stock.Proof.HelperAliasClassDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.ClassGrowthDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Actual original context construction initializes alias classes and all
reserved term-context class/virtual-register facts without an input certificate. -/
theorem stock_build_alias_class_inputs {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial)) :
    AliasClasses initial ∧ ReservedClasses ctx initial ∧
      ∀ ti data,ReservedClasses {Driver.termCtx ctx ti data with tryRegs := initial.tryRegs[ti]!} initial := by
  obtain ⟨original,old,requests,legacy,_,same⟩ := buildCtx_allocation build
  have alias : initial.alias = #[] := by
    have state := congrArg (fun q : Ctx × Array (Nat × Nat) × State => q.2.2) same
    change initial = _ at state
    rw [state]
    rfl
  have context := congrArg (fun q : Ctx × Array (Nat × Nat) × State => q.1.tryRegs) same
  change ctx.tryRegs = original.tryRegs at context
  rw [(ctxSpec_of legacy).facts.tryRegs] at context
  obtain ⟨size,values,reserved⟩ := InitialClassesDraft.stock_build_classes build
  refine ⟨?_,?_,?_⟩
  · intro key target entry
    rw [alias] at entry
    simp at entry
  · intro r member
    rw [context] at member
    simp at member
  · intro ti data r member
    change r ∈ initial.tryRegs[ti]!.1 ++ initial.tryRegs[ti]!.2 at member
    cases found : initial.tryRegs[ti]? with
    | none => simp only [getElem!_def,found,Option.getD_none] at member; cases member
    | some rs =>
      simp only [getElem!_def,found,Option.getD_some] at member
      obtain ⟨n,shape,_⟩ := buildCtx_reservedBelow build ti rs found r member
      exact ⟨reserved ti rs found r member,n,shape⟩

/-- At a later actual class-growing state with unchanged reservation table,
original context construction still supplies the selected term's complete
reservation-class invariant; this is internal driver state, not source scope. -/
theorem stock_built_reserved_class_inputs {f : Clif.Function} {ctx : Ctx}
    {ranges : Array (Nat × Nat)} {initial before : State}
    (build : Stock.buildCtx f = .ok (ctx,ranges,initial))
    (growth : ClassGrowth initial before) (same : before.tryRegs = initial.tryRegs) (ti : Nat) (data : V) :
    ReservedClasses {Driver.termCtx ctx ti data with tryRegs := before.tryRegs[ti]!} before := by
  intro r member
  change r ∈ before.tryRegs[ti]!.1 ++ before.tryRegs[ti]!.2 at member
  rw [same] at member
  have initialized := (stock_build_alias_class_inputs build).2.2 ti data r member
  exact intCls_step growth initialized

end Backend.Stock.Proof.HelperAliasClassDraft
