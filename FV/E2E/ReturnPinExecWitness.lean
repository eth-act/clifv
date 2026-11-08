import FV.E2E.ReturnPinExecProven
import FV.E2E.ReturnPinBinaryWitness
import FV.E2E.ProductionBoundaryWitness

namespace E2E.ReturnPinExecWitness
open Backend Backend.Proof E2E.LinkCheck E2E.SemanticBinary E2E.SemanticExecBytes
open E2E.ReturnPinBinaryWitness
set_option autoImplicit false
set_option Elab.async false

theorem code_map (cleanup : Bool) : codeMapB (original cleanup) (tabOf (original cleanup).results) = true :=
  Link.ProductionCompiler.codeMap_leanLink (Link.ProductionCompiler.attempt_spec
    (ProductionBoundaryWitness.compiler_success cleanup)).2

theorem got (cleanup : Bool) : GotOk (original cleanup) (ProductionBoundaryWitness.file cleanup) :=
  Link.ProductionCompiler.gotOk_leanLink (Link.ProductionCompiler.attempt_spec
    (ProductionBoundaryWitness.compiler_success cleanup)).2

theorem avoids (cleanup : Bool) (word : BitVec 64) (N : Nat) :
    OutsideAvoids (GotSlot (original cleanup) (ProductionBoundaryWitness.file cleanup))
      ProductionBoundaryWitness.f N (ProductionBoundaryWitness.machine cleanup word)
      [ProductionBoundaryWitness.argument word] (ProductionBoundaryWitness.entered cleanup) := by
  have old := Link.ProductionCompiler.outsideAvoids_leanLink (Link.ProductionCompiler.attempt_spec
    (ProductionBoundaryWitness.compiler_success cleanup)).2 ProductionBoundaryWitness.f N
    (ProductionBoundaryWitness.machine cleanup word) [ProductionBoundaryWitness.argument word]
    (ProductionBoundaryWitness.entered cleanup)
  exact ⟨old.stack,old.args,old.valid⟩

def ExecReturn (cleanup : Bool) (word : BitVec 64) : Prop :=
  ExecRefines (art (original cleanup) ProductionBoundaryWitness.f).fb
    (art (original cleanup) ProductionBoundaryWitness.f).base
    (xreg 30 (ProductionBoundaryWitness.machine cleanup word))
    (step (original cleanup) closedBase (ProductionBoundaryWitness.file cleanup))
    (ProductionBoundaryWitness.machine cleanup word)
    (BinCheck.RelocAtWithResults (original cleanup) (original cleanup).results)
    (.returned [ProductionBoundaryWitness.argument word] (ProductionBoundaryWitness.cm cleanup))

theorem ordinary (cleanup : Bool) (word : BitVec 64) : ExecReturn cleanup word := by
  have base : BaseOk (sys (original cleanup) closedBase) := ProductionBoundaryWitness.base_ok cleanup
  have found := ProductionBoundaryWitness.program_find cleanup
  have contract := ReturnPinBinary.okB_sound (checked cleanup) (baseOk_F (F' := img (original cleanup)) base)
    (fun _ h => h)
  have returned := ProductionBoundaryWitness.source_returns cleanup word
  have traps := ReturnPinBinary.trapsExplicit_of_run contract (Clif.Program.func?_some found).1
    (source_run cleanup word).entry (outside cleanup word).symbols returned
  have good : SemanticStackBound.goodN (original cleanup) ProductionBoundaryWitness.name = true :=
    (ProductionBoundaryWitness.concrete_facts cleanup).2.2.1
  obtain ⟨f,found',cycle⟩ := (ReturnPinStackBound.goodN_iff (checked cleanup)).1 good
  have equal : f = ProductionBoundaryWitness.f := Option.some.inj (found'.symm.trans found)
  subst f
  have result := ReturnPinExecBytes.binary_correct_exec_proven (checked cleanup) (code_map cleanup)
    (Link.ProductionImageProof.bin_ok (Link.ProductionCompiler.attempt_spec
      (ProductionBoundaryWitness.compiler_success cleanup)).2) (got cleanup) closedBase base
    (hooksSim_closed _) found cycle 3 (intact cleanup word) (outside cleanup word)
    (avoids cleanup word _) (source_run cleanup word) traps
  rw [returned] at result
  exact result

theorem recursive_depth (cleanup : Bool) (word : BitVec 64) : ExecReturn cleanup word := by
  have base : BaseOk (sys (original cleanup) closedBase) := ProductionBoundaryWitness.base_ok cleanup
  have found := ProductionBoundaryWitness.program_find cleanup
  have contract := ReturnPinBinary.okB_sound (checked cleanup) (baseOk_F (F' := img (original cleanup)) base)
    (fun _ h => h)
  have returned := ProductionBoundaryWitness.source_returns cleanup word
  have traps := ReturnPinBinary.trapsExplicit_of_run contract (Clif.Program.func?_some found).1
    (source_run cleanup word).entry (outside cleanup word).symbols returned
  have entry := outside_budget cleanup word _ (depth_budget cleanup)
  have result := ReturnPinExecBytes.binary_correct_exec_depth_proven (checked cleanup) (code_map cleanup)
    (Link.ProductionImageProof.bin_ok (Link.ProductionCompiler.attempt_spec
      (ProductionBoundaryWitness.compiler_success cleanup)).2) (got cleanup) closedBase base
    (hooksSim_closed _) found 3 (intact cleanup word) entry (avoids cleanup word _)
    (source_run cleanup word) traps
  rw [returned] at result
  exact result

theorem peak_depth (cleanup : Bool) (word : BitVec 64) : ExecReturn cleanup word := by
  have base : BaseOk (sys (original cleanup) closedBase) := ProductionBoundaryWitness.base_ok cleanup
  have found := ProductionBoundaryWitness.program_find cleanup
  have contract := ReturnPinBinary.okB_sound (checked cleanup) (baseOk_F (F' := img (original cleanup)) base)
    (fun _ h => h)
  have returned := ProductionBoundaryWitness.source_returns cleanup word
  have bounded := depth cleanup word
  have traps := ReturnPinBinary.trapsExplicit_of_runD contract (Clif.Program.func?_some found).1
    (source_run cleanup word).entry (outside cleanup word).symbols bounded returned
  have budget : frameDrop (art (original cleanup) ProductionBoundaryWitness.f).af +
      ((original cleanup).D*0 + pbMax (original cleanup)) ≤ 4096 := by
    have bound := depth_budget cleanup
    omega
  have entry := outside_budget cleanup word _ budget
  have result := ReturnPinExecBytes.binary_correct_exec_peak_proven (checked cleanup) (code_map cleanup)
    (Link.ProductionImageProof.bin_ok (Link.ProductionCompiler.attempt_spec
      (ProductionBoundaryWitness.compiler_success cleanup)).2) (got cleanup) closedBase base
    (hooksSim_closed _) found 3 0 (intact cleanup word) entry (avoids cleanup word _)
    (source_run cleanup word) bounded traps
  rw [returned] at result
  exact result

end E2E.ReturnPinExecWitness
