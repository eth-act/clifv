import FV.Backend.StockMemoryStoreCheck
import FV.Backend.Proof.StockMemoryStoreClassWitness
import FV.Backend.Proof.StockMemoryStoreRecordFixture

namespace E2E.StockMemoryStoreFunctionWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.StoreRoots Backend.Stock.Memory.StoreRoots.Fixture
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

/-- Original source functions positively inhabit the executable store selector. -/
theorem source_selector_witness (kind : Kind) : Backend.Stock.MemoryStore.sourceOk (function kind) = true := by
  simp only [Backend.Stock.MemoryStore.sourceOk,Bool.and_eq_true,Bool.not_eq_true']
  refine ⟨⟨⟨⟨⟨?_,?_⟩,?_⟩,(source_class_witness kind).abi⟩,
    (source_class_witness kind).ordinary⟩,?_⟩
  · cases kind <;> rfl
  · cases kind <;> decide +kernel
  · apply dominatedB_of_facts ?_ (dominated kind)
    change nodupB [0,1] = true
    simp [nodupB]
  · cases kind <;> rfl

end E2E.StockMemoryStoreFunctionWitness
