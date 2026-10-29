module

public import FV.Backend.Proof.StockLogicalCheck
public import FV.Backend.Proof.StockLogicalSourceWitness

@[expose] public section

namespace Backend.Stock.Logical
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof.LogicalSemantics
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

/-- Reflection of an existing dominance proof avoids kernel execution of the
hash-based availability algorithm. This helper changes no input condition. -/
private theorem dominatedB_of_facts {f : Clif.Function}
    (unique : nodupB (valueDefs f) = true) (dominated : Dominated f) : dominatedB f = true := by
  simp only [dominatedB,unique,Bool.true_and]
  cases built : Backend.buildCtx f with
  | error message => rfl
  | ok output =>
    obtain ⟨ctx,ranges,st⟩ := output
    simp only
    apply List.all_eq_true.mpr
    intro bi member
    cases block : f.blocks[bi]? with
    | none => simp only [block]
    | some b =>
      simp only [block,Bool.and_eq_true,List.all_eq_true]
      have facts := ctxFacts_of built
      have defs : DefsAt ctx b (startOnly (blockStart f bi)).start := fun k stm atStatement r contains =>
        (facts.defs dominated.ssa r _).mpr ⟨bi,b,k,stm,block,atStatement,contains,rfl⟩
      refine ⟨⟨?_,?_⟩,?_⟩
      · intro j member
        cases statement : b.body[j]? with
        | none => simp only [statement]
        | some stm =>
          simp only [statement,List.all_eq_true]
          intro y contains
          exact (mem_avail block defs).mp ((dominated.uses _ _ _ built bi b block).1 j stm statement y contains)
      · intro y contains
        exact (mem_avail block defs).mp ((dominated.uses _ _ _ built bi b block).2 y contains)
      · intro x available
        simp only [Bool.or_eq_true,Std.HashSet.contains_ofList,List.contains_iff_mem,
          List.all_eq_true,Bool.not_eq_true',Bool.eq_false_iff,ne_eq]
        by_cases isLocal : x ∈ defsOf f bi
        · exact .inl isLocal
        · exact .inr (dominated.paramFree _ _ _ built bi x available isLocal)

/-- A nonempty sparse-ID logical source inhabits every source-class guard. -/
theorem classifier_accepts : sourceOk (formFunction .registers) = true := by
  simp only [sourceOk,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,?_⟩,by decide +kernel⟩
  apply dominatedB_of_facts ?_ Backend.Stock.Proof.LogicalSelected.logical_register_source_dominated
  change nodupB [7,31,100] = true
  simp [nodupB]

private def actualChecked : Bool :=
  match Stock.lower (formFunction .registers) with
  | .error _ => false
  | .ok result => check (formFunction .registers) result.code

/-- Fixed-data actual lowering/provenance check; no native axiom enters the
universal checker soundness roots. -/
theorem actualChecked_true : actualChecked = true := by native_decide

/-- A real successful whole-driver output inhabits checker soundness with a
nonempty logical body and the original source domain, without supplied proofs. -/
theorem actual_check_witness :
    ∃ result, Stock.lower (formFunction .registers) = .ok result ∧
      check (formFunction .registers) result.code = true ∧
      Domain (formFunction .registers) ∧
      (formFunction .registers).blocks[0]!.body ≠ [] := by
  have accepted := actualChecked_true
  cases run : Stock.lower (formFunction .registers) with
  | error message => simp only [actualChecked,run] at accepted; cases accepted
  | ok result =>
    simp only [actualChecked,run] at accepted
    exact ⟨result,rfl,accepted,sourceOk_sound classifier_accepts,by decide⟩

end Backend.Stock.Logical
