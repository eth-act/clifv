import FV.Backend.Proof.StockAcquireShapeCheck
import FV.Backend.Proof.StockAcquire810Witness
import FV.Backend.Proof.StockAcquirePrepare

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.lower

/-- The actual production cleanup choice, without a new input classifier. -/
def acquire_stage (cleanup : Bool) (vc : VCode) : VCode :=
  if cleanup then DeadCleanup.prune vc else vc

private def shapes_observed : Option Bool :=
  (Stock.lower function).toOption.map fun result =>
    [false,true].all fun cleanup =>
      (prepare (acquire_stage cleanup result.code)).toOption.any fun prepared =>
        prepCheck (acquire_stage cleanup result.code) prepared &&
          prepared.blocks.all (fun block => block.insts.all acquireByteShapeB)

private theorem shapes_observed_true : shapes_observed = some true := by native_decide

/-- Both actual preparation modes retain only the required ordinary access forms.
The shape proof is internal and does not restrict source arguments or memory. -/
theorem prepared_acquire_shapes {result : Result}
    (lowered : Stock.lower function = .ok result) (cleanup : Bool) :
    ∃ prepared,prepare (acquire_stage cleanup result.code) = .ok prepared ∧
      prepCheck (acquire_stage cleanup result.code) prepared = true ∧
      ∀ (b : Nat) (block : VBlock) (j : Nat) (inst : MInst),
        prepared.blocks[b]? = some block → block.insts[j]? = some inst →
        ∀ (uses : List CV) (world : Arm.ArmState) (code : Clif.TrapCode)
          (address : BitVec 64) (bytes : Nat),
          AcquireAt inst uses world code address bytes → (∃ d pointer flags,inst = .loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags) := by
  have observed := shapes_observed_true
  unfold shapes_observed at observed
  rw [lowered] at observed
  have both := Option.some.inj observed
  have member : cleanup ∈ [false,true] := by cases cleanup <;> simp
  have mode := List.all_eq_true.mp both cleanup member
  obtain ⟨prepared,found,checked,shapes⟩ := (by
    simpa only [Option.any_eq_true,Bool.and_eq_true] using mode :
      ∃ prepared,(prepare (acquire_stage cleanup result.code)).toOption = some prepared ∧
        prepCheck (acquire_stage cleanup result.code) prepared = true ∧
        prepared.blocks.all (fun block => block.insts.all acquireByteShapeB) = true)
  have prepareRun : prepare (acquire_stage cleanup result.code) = .ok prepared := by
    cases run : prepare (acquire_stage cleanup result.code) with
    | error message => simp only [run,Except.toOption] at found; contradiction
    | ok actual => simp only [run,Except.toOption] at found; cases found; rfl
  refine ⟨prepared,prepareRun,checked,?_⟩
  intro b block j inst present located uses world code address bytes access
  have blockCheck := (Array.all_eq_true_iff_forall_mem.mp shapes) block (Array.mem_of_getElem? present)
  have instCheck := (Array.all_eq_true_iff_forall_mem.mp blockCheck) inst (Array.mem_of_getElem? located)
  exact acquireByteShape_of_check instCheck access

end Backend.Stock.Proof.Acquire810
