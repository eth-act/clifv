import FV.Backend.Proof.StockFenceCompiledWitness

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Stock.lower

private theorem except_of_toOption {α : Type} {value : Except String α} {out : α}
    (observed : value.toOption = some out) : value = .ok out := by
  cases value with
  | error message => cases observed
  | ok result => cases observed; rfl

private theorem unit_of_isOk {value : Except String Unit} (checked : value.isOk = true) :
    value = .ok () := by
  cases value with
  | error message => cases checked
  | ok result => cases result; rfl

private theorem bind_some {α β : Type} (value : Option α) (next : α → Option β)
    {out : β} (run : (value >>= next) = some out) :
    ∃ input,value = some input ∧ next input = some out := by
  cases value with
  | none => cases run
  | some input => exact ⟨input,rfl,run⟩

/-- Every artifact returned by the actual checked pipeline retains all original stage equations. -/
theorem mixed_compile_sound {cleanup : Bool} {artifact : MixedArtifacts}
    (run : mixed_compile cleanup = some artifact) :
    CompiledStockArithmeticStage function cleanup 0 artifact.result artifact.prepared
      artifact.allocated artifact.physical artifact.assembly artifact.binary := by
  unfold mixed_compile at run
  obtain ⟨result,lowered,step1⟩ := bind_some _ _ run
  obtain ⟨prepared,preparation,step2⟩ := bind_some _ _ step1
  obtain ⟨physical,allocated,step3⟩ := bind_some _ _ step2
  obtain ⟨assembly,emitted,step4⟩ := bind_some _ _ step3
  obtain ⟨binary,layout,last⟩ := bind_some _ _ step4
  split at last
  · rename_i checked
    simp only [Bool.and_eq_true] at checked
    cases Option.some.inj last
    exact ⟨
      except_of_toOption lowered,except_of_toOption preparation,checked.1,unit_of_isOk checked.2,
      except_of_toOption allocated,except_of_toOption emitted,except_of_toOption layout⟩
  · cases last

private theorem covered_observed : [false,true].all (fun cleanup =>
    (mixed_compile cleanup).any fun artifact =>
      formsCoveredB ⟨artifact.assembly.k,artifact.physical.slotBase⟩ artifact.prepared) = true := by
  native_decide

/-- Both actual checked modes also discharge every machine form internally. -/
theorem mixed_complete_covered_compilation (cleanup : Bool) :
    ∃ artifact : MixedArtifacts,mixed_compile cleanup = some artifact ∧
      CompiledStockArithmeticStage function cleanup 0 artifact.result artifact.prepared
        artifact.allocated artifact.physical artifact.assembly artifact.binary ∧
      FormsCovered ⟨artifact.assembly.k,artifact.physical.slotBase⟩ artifact.prepared := by
  have member : cleanup ∈ [false,true] := by cases cleanup <;> simp
  have observed := List.all_eq_true.mp covered_observed cleanup member
  obtain ⟨artifact,run,covered⟩ := Option.any_eq_true.mp observed
  exact ⟨artifact,run,mixed_compile_sound run,(formsCoveredB_iff _ _).mp covered⟩

end Backend.Stock.Proof.FenceFixture
