import FV.Backend.Lowering.StockConditionalRankedCfg
import FV.Backend.Proof.StockParameterCheck
import FV.Backend.Proof.StockParameterFixture

namespace Backend.Stock.Proof.ParameterCfg.Fixture
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.ForwardSource Backend.Stock.Proof.ConditionalValues
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 16000000
private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl

theorem dominated : Dominated function := by
  constructor
  · change ([7,31,47,59] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    have bound : bi < 4 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 ∨ bi = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      simp [function] at found
      subst b
      constructor
      · intro j stm present
        cases j <;> simp [function] at present
        all_goals subst stm; intro x member; cases member
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member <;>
          subst x <;> simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have values : x = 7 ∨ x = 31 ∨ x = 47 ∨ x = 59 := by simpa [valueDefs,function] using fixed.2.2.2.1
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    rcases values with rfl | rfl | rfl | rfl
    all_goals change y ∈ ([] : List Nat) at member; cases member

theorem scope : LowerScope function := lowerScope_of rfl

theorem source_cases :
    Clif.enterFunc function [⟨.i64,1⟩] Clif.Mem.empty = .ok (initial 1,Clif.Mem.empty) ∧
    Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial 1,[],Clif.Mem.empty⟩ = .returned [⟨.i64,1⟩] Clif.Mem.empty ∧
    Clif.runLoop Clif.Env.empty {funcs := []} 4 ⟨initial 0,[],Clif.Mem.empty⟩ = .returned [⟨.i64,2⟩] Clif.Mem.empty :=
  ⟨rfl,rfl,rfl⟩
theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
  have all : function.blocks.all (fun b => b.body.all Scalar.maskMixedBodyEligible) = true := rfl
  intro b member stm present
  exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp (List.all_eq_true.mp all b member) stm present)


theorem selector_witness : Stock.ParameterCfg.sourceEligible function = true ∧
    Stock.ParameterCfg.hasNonentryConditional function = true ∧
    Stock.ConditionalCfg.rankedEligible function = false := ⟨rfl,rfl,rfl⟩
theorem ranked : Ranked function id := (Stock.ParameterCfg.source_eligible_facts selector_witness.1).2.1
theorem all_parameter_terms : ParameterTerms function := (Stock.ParameterCfg.source_eligible_facts selector_witness.1).1
theorem nonentry_terms : NonentryParameterTerms function := parameter_terms_nonentry all_parameter_terms
theorem original_domain_witness : Scalar.Domain function :=
  Stock.ParameterCfg.domain_of_source_eligible selector_witness.1 scope dominated rfl

namespace Trap
theorem source_cases :
    Clif.enterFunc function [⟨.i64,0⟩] Clif.Mem.empty = .ok (initial 0,Clif.Mem.empty) ∧
    Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial 0,[],Clif.Mem.empty⟩ = .trapped .intDivz ∧
    Clif.runLoop Clif.Env.empty {funcs := []} 5 ⟨initial 1,[],Clif.Mem.empty⟩ = .returned [⟨.i64,1⟩] Clif.Mem.empty :=
  ⟨rfl,rfl,rfl⟩

private def original : Ctx × Array (Nat × Nat) × LState :=
  (Backend.buildCtx function).toOption.getD (sinkCtx,#[],default)
private theorem original_build : Backend.buildCtx function = .ok original := rfl
theorem dominated : Dominated function := by
  constructor
  · change ([7,31,47,59,60] : List Nat).Nodup; decide +kernel
  · intro ctx ranges st build bi b found
    have bound : bi < 4 := by have h := lt_of_getElem? found; simpa [function] using h
    have cases : bi = 0 ∨ bi = 1 ∨ bi = 2 ∨ bi = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals
      simp [function] at found
      subst b
      constructor
      · intro j stm present
        have cases : j = 0 ∨ j = 1 := by
          have bound := lt_of_getElem? present
          simp only [List.length_cons,List.length_nil] at bound
          omega
        rcases cases with rfl | rfl
        all_goals simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,List.getElem?_nil,
          Option.some.injEq,reduceCtorEq] at present
        all_goals subst stm; intro x member; simp [Driver.instArgs] at member
        all_goals subst x; simp [availOf,function,defsBefore,defsFrom]
      · intro x member
        simp [abiTerm,Driver.termArgs,sretRet,sigRets,function] at member <;>
          subst x <;> simp [availOf,function,defsBefore,defsFrom]
  · intro ctx ranges st build tl x available notLocal y member
    have fixed := (inFix_fixOk (f := function) (ctx := ctx) (gn := id)).cand tl x available
    have values : x = 7 ∨ x = 31 ∨ x = 47 ∨ x = 59 ∨ x = 60 := by simpa [valueDefs,function] using fixed.2.2.2.1
    have context : ctx = original.1 := congrArg Prod.fst (Except.ok.inj (build.symm.trans original_build))
    rw [context] at member
    rcases values with rfl | rfl | rfl | rfl | rfl
    all_goals try (change y ∈ ([] : List Nat) at member; cases member)
    change y ∈ [59,59] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
    subst y
    have bound : tl < 4 := by simpa [function] using fixed.2.1
    have choices : tl = 0 ∨ tl = 1 ∨ tl = 2 ∨ tl = 3 := by omega
    rcases choices with rfl | rfl | rfl | rfl <;> simp [parsOf,function]


theorem scope : LowerScope function := lowerScope_of rfl

theorem selector_witness : Stock.ParameterCfg.sourceEligible function = true ∧
    Stock.ParameterCfg.hasNonentryConditional function = true ∧
    Stock.ConditionalCfg.rankedEligible function = false := ⟨rfl,rfl,rfl⟩
theorem ranked : Ranked function id := (Stock.ParameterCfg.source_eligible_facts selector_witness.1).2.1
theorem all_parameter_terms : ParameterTerms function := (Stock.ParameterCfg.source_eligible_facts selector_witness.1).1
theorem nonentry_terms : NonentryParameterTerms function := parameter_terms_nonentry all_parameter_terms
theorem family : ∀ b ∈ function.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst :=
  (Stock.ParameterCfg.source_eligible_facts selector_witness.1).2.2.1
theorem original_domain_witness : Scalar.Domain function :=
  Stock.ParameterCfg.domain_of_source_eligible selector_witness.1 scope dominated rfl
end Trap
end Backend.Stock.Proof.ParameterCfg.Fixture
