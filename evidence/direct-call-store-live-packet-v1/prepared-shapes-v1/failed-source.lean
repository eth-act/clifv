import FV.E2E.StockCallStoreCompiledWitness
import FV.Backend.Proof.StockMemoryAccessShapeCheck

namespace E2E.CallStoreCompiledWitness
open Backend Backend.Proof Backend.Proof.Driver Backend.Stock.Proof MemoryFaults CallStoreFixture
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private def shapesObserved (cleanup : Bool) : Bool :=
  (Stock.lower caller).toOption.any fun result =>
    (prepare (Stock.Arithmetic.stage cleanup result.code)).toOption.any fun prepared =>
      prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared &&
        prepared.blocks.all (fun block => block.insts.all ordinaryAccessShapeB)
attribute [local irreducible] shapesObserved
-- witness: native_decide (the fixed original artifact shapes in both preparation modes)
private theorem shapesObserved_true (cleanup : Bool) : shapesObserved cleanup = true := by
  cases cleanup <;> native_decide

private theorem observedAvailable {α : Type} {action : Except String α} {predicate : α → Bool}
    (positive : action.toOption.any predicate = true) : ∃ value,action = .ok value ∧ predicate value = true := by
  cases action with
  | error message => cases positive
  | ok value => exact ⟨value,rfl,positive⟩

/-- The original checked artifacts discharge the ordinary store shape obligation internally. -/
-- witness: native_decide (fixed original source and actual prepared artifacts only)
theorem prepared_access_shapes {result : Stock.Result}
    (lowered : Stock.lower caller = .ok result) (cleanup : Bool) :
    ∃ prepared,prepare (Stock.Arithmetic.stage cleanup result.code) = .ok prepared ∧
      prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared = true ∧
      ∀ (b : Nat) (block : VBlock) (j : Nat) (inst : MInst),prepared.blocks[b]? = some block → block.insts[j]? = some inst →
        ∀ sb uses world code address bytes,
          AccessAt sb inst uses world code address bytes → OrdinaryAccessShape inst := by
  have observed := shapesObserved_true cleanup
  unfold shapesObserved at observed
  rw [lowered] at observed
  obtain ⟨prepared,found,checked⟩ := observedAvailable observed
  obtain ⟨accepted,shapes⟩ := Bool.and_eq_true_iff.mp checked
  refine ⟨prepared,found,accepted,?_⟩
  intro b block j inst present located sb uses world code address bytes access
  exact ordinaryAccessShapes_of_check shapes b block j inst present located access

end E2E.CallStoreCompiledWitness
