import FV.Backend.Proof.StockMemoryExtLoadCheck
import FV.E2E.StockMemoryExtLoadPairedFunctionWitness

namespace Backend.Stock.MemoryExtending
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory.ExtendedRoots
open Backend.Stock.Memory.ExtendedRoots.Fixture E2E.StockMemoryExtLoadFunctionWitness
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

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

/-- Each extending form passes the actual executable source checker. -/
theorem checked_source_class_witness (kind : Kind) :
    sourceOk (function kind) = true ∧ ∃ chosen ty,SingleClass chosen ty (function kind) := by
  have accepted : sourceOk (function kind) = true := by
    simp only [sourceOk,Bool.and_eq_true,Bool.not_eq_true']
    refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,(source_class_witness kind).abi⟩,
      (source_class_witness kind).ordinary⟩,rfl⟩
    · cases kind <;> rfl
    · cases kind <;> decide +kernel
    · apply dominatedB_of_facts ?_ (dominated kind)
      change nodupB [0,2] = true
      simp [nodupB]
  exact ⟨accepted,sourceOk_sound accepted⟩

/-- Plain loads retain the previously published provider. -/
theorem plain_load_excluded (kind : Kind) :
    eligible {function kind with blocks := [{(function kind).blocks[0]! with
      body := [⟨[2],.load .load .i64 flags 0 0⟩]}]} = false := by
  cases kind <;> rfl

end Backend.Stock.MemoryExtending
