import FV.Backend.Proof.StockTryAliasObservation
import FV.Backend.Proof.StockTryAliasTerms
import FV.Backend.Proof.StockScanAliasClasses

namespace Backend.Stock.Proof.HelperAliasWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.Flow Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.BindingClassDraft Backend.Stock.Proof.HelperAliasClassDraft Backend.Stock.Proof.TryAliasFixture
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower Stock.externCtor

private theorem lower_build {f : Clif.Function} {result : Result} (run : Stock.lower f = .ok result) :
    ∃ ranges,Stock.buildCtx f = .ok (result.ctx,ranges,result.initial) := by
  unfold Stock.lower at run
  dsimp only at run
  repeat' first
    | (solve | cases run)
    | simp only [bind,Except.bind,pure,Except.pure] at run
    | split at run
  cases run
  exact ⟨_,by assumption⟩

/-- A complete actual original-condition try-call source, indexed preparation,
global checked fallback and physical lowering inhabit nonempty return/payload
alias classes. The actual helper, exported interpreter term and named root all
write payload194 to return193; actual returned/prepared code contains tryCall. -/
theorem stock_complete_try_alias_classes_witness :
    ∃ (result : Result) (p : EdgeVCode) (rf : RFunc) (af : AFunc) (ranges : Array (Nat × Nat))
      (value : Backend.V) (after : State),
      Stock.lower function = .ok result ∧ LowerScope function ∧ Dominated function ∧ ArityOk function ∧
      prepareAt result.code result.edgeArgs = .ok p ∧ rf = spillAllocAt p.code p.edges ∧
      checkAllocAt p.code p.edges rf = .ok () ∧ lowerRFunc p.code rf = .ok af ∧
      Stock.buildCtx function = .ok (result.ctx,ranges,result.initial) ∧
      result.initial.tryRegs[1]? = some ([.vreg 193 .int],[.vreg 194 .int,.vreg 195 .int]) ∧
      AliasClasses result.initial ∧ ReservedClasses (context result) result.initial ∧
      Stock.externCtor (context result) T.gen_try_call_rets [.op (.sig signature)] result.initial = .ok (value,after) ∧
      (applyTerm program (Stock.sem (context result)) {} 1 T.gen_try_call_rets.ret 300
        [.op (.sig signature)]).run (result.initial,#[]) = .ok (some value,after,#[]) ∧
      Stock.runTerm (context result) "gen_try_call_rets" [.op (.sig signature)] result.initial = .ok (some value,after,[]) ∧
      (after.alias[194]?).join = some 193 ∧ (result.final.alias[194]?).join = some 193 ∧
      AliasClasses after ∧ ReservedClasses (context result) after ∧
      ReservedClasses {Driver.termCtx result.ctx 1 (.op .unit) with tryRegs := after.tryRegs[1]!} after ∧
      result.code.blocks.any (fun b => b.insts.any isTryCall) = true ∧
      p.code.blocks.any (fun b => b.insts.any isTryCall) = true := by
  have actual := observed
  unfold Observed at actual
  cases run : pipeline with
  | error err => simp only [run,Except.toOption,Option.map_none] at actual; cases actual
  | ok q =>
    rw [run] at actual
    simp only [Except.toOption,Option.map_some,Option.some.injEq,Bool.and_eq_true,decide_eq_true_eq] at actual
    unfold pipeline at run
    obtain ⟨result,lowered,h⟩ := Except.bind_ok run
    obtain ⟨prepared,prepare,h⟩ := Except.bind_ok h
    obtain ⟨rf,selected,h⟩ := Except.bind_ok h
    obtain ⟨af,physical,h⟩ := Except.bind_ok h
    cases ctor : Stock.externCtor (context result) T.gen_try_call_rets [.op (.sig signature)] result.initial with
    | fail => simp only [ctor] at h; cases h
    | unmodeled err => simp only [ctor] at h; cases h
    | ok pair =>
      rcases pair with ⟨value,after⟩
      simp only [ctor,pure,Except.pure] at h
      cases h
      obtain ⟨⟨⟨slot,afterAlias,finalAlias⟩,rawTry⟩,preparedTry⟩ := actual
      have accepted := PerEdge.allocResultAt_checked selected
      have fallback : rf = spillAllocAt prepared.code prepared.edges := by
        unfold allocResultAt checkedSpillAt at selected
        simp only [bind,Except.bind] at selected
        split at selected <;> cases selected
        rfl
      obtain ⟨ranges,build⟩ := lower_build lowered
      have inputs := stock_build_alias_class_inputs build
      have reserved : ReservedClasses (context result) result.initial := inputs.2.2 1 (.op .unit)
      have applyRun : (applyTerm program (Stock.sem (context result)) {} 1 T.gen_try_call_rets.ret 300
          [.op (.sig signature)]).run (result.initial,#[]) = .ok (some value,after,#[]) := by
        simp only [applyTerm.eq_2,try_term,Stock.sem,T.gen_try_call_rets,isel_data,isel_monad]
        have call := ctor
        unfold T.gen_try_call_rets at call
        rw [call]
        rfl
      have named : Stock.runTerm (context result) "gen_try_call_rets" [.op (.sig signature)] result.initial =
          .ok (some value,after,[]) := by
        unfold Stock.runTerm Isle.Interp.run
        rw [try_lookup]
        dsimp only
        simp only [applyTerm.eq_2,try_term,Stock.sem,T.gen_try_call_rets,isel_data,isel_monad]
        have call := ctor
        unfold T.gen_try_call_rets at call
        rw [call]
        rfl
      have byCtor := stock_ctor_alias_classes reserved inputs.1 ctor
      have byApply := stock_apply_alias_classes reserved inputs.1 applyRun
      have byNamed := stock_named_alias_classes reserved inputs.1 named
      exact ⟨result,prepared,rf,af,ranges,value,after,lowered,source_scope,source_dominated,source_arity,
        prepare,fallback,accepted,physical,build,slot,inputs.1,reserved,ctor,applyRun,named,afterAlias,finalAlias,
        byCtor,byNamed.2,
        stock_built_reserved_class_inputs build (ClassGrowthDraft.stock_ctor_classGrowth ctor)
          (stock_ctor_allocationLe ctor).2 1 (.op .unit),rawTry,preparedTry⟩

end Backend.Stock.Proof.HelperAliasWitnessDraft
