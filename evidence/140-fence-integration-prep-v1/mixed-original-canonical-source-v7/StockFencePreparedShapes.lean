import FV.Backend.Proof.StockMemoryAccessShapeCheck
import FV.Backend.Proof.StockFenceWitness
import FV.Backend.Proof.StockMemoryAccessPrepare

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver MemoryFaults
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.lower

/-- The actual production cleanup choice, without a new input classifier. -/
def mixed_stage (cleanup : Bool) (vc : VCode) : VCode :=
  if cleanup then DeadCleanup.prune vc else vc

private def shapes_observed : Option Bool :=
  (Stock.lower function).toOption.map fun result =>
    [false,true].all fun cleanup =>
      (prepare (mixed_stage cleanup result.code)).toOption.any fun prepared =>
        prepCheck (mixed_stage cleanup result.code) prepared &&
          prepared.blocks.all (fun block => block.insts.all ordinaryAccessShapeB)

private theorem shapes_observed_true : shapes_observed = some true := by native_decide

/-- Both actual preparation modes retain only the required ordinary access forms.
The shape proof is internal and does not restrict source arguments or memory. -/
theorem mixed_prepared_access_shapes {result : Result}
    (lowered : Stock.lower function = .ok result) (cleanup : Bool) :
    ∃ prepared,prepare (mixed_stage cleanup result.code) = .ok prepared ∧
      prepCheck (mixed_stage cleanup result.code) prepared = true ∧
      ∀ (b : Nat) (block : VBlock) (j : Nat) (inst : MInst),
        prepared.blocks[b]? = some block → block.insts[j]? = some inst →
        ∀ (sb : Nat) (uses : List CV) (world : Arm.ArmState) (code : Clif.TrapCode)
          (address : BitVec 64) (bytes : Nat),
          AccessAt sb inst uses world code address bytes → OrdinaryAccessShape inst := by
  have observed := shapes_observed_true
  unfold shapes_observed at observed
  rw [lowered] at observed
  have both := Option.some.inj observed
  have member : cleanup ∈ [false,true] := by cases cleanup <;> simp
  have mode := List.all_eq_true.mp both cleanup member
  obtain ⟨prepared,found,checked,shapes⟩ := (by
    simpa only [Option.any_eq_true,Bool.and_eq_true] using mode :
      ∃ prepared,(prepare (mixed_stage cleanup result.code)).toOption = some prepared ∧
        prepCheck (mixed_stage cleanup result.code) prepared = true ∧
        prepared.blocks.all (fun block => block.insts.all ordinaryAccessShapeB) = true)
  have prepareRun : prepare (mixed_stage cleanup result.code) = .ok prepared := by
    cases run : prepare (mixed_stage cleanup result.code) with
    | error message => simp only [run,Except.toOption] at found; contradiction
    | ok actual => simp only [run,Except.toOption] at found; cases found; rfl
  refine ⟨prepared,prepareRun,checked,?_⟩
  intro b block j inst present located sb uses world code address bytes access
  exact ordinaryAccessShapes_of_check shapes b block j inst present located access

end Backend.Stock.Proof.FenceFixture
