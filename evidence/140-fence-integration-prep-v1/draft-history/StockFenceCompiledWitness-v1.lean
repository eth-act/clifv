import FV.Backend.Proof.StockFenceMachine

namespace Backend.Stock.Proof.FenceFixture
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
attribute [local irreducible] Stock.lower

/-- Actual artifacts from the unchanged compiler stages. -/
structure MixedArtifacts where
  result : Stock.Result
  prepared : VCode
  allocated : RFunc
  physical : AFunc
  assembly : FnAsm
  binary : FnBin

/-- An inhabited checked pipeline uses the existing all-stack allocation. -/
def mixed_compile (cleanup : Bool) : Option MixedArtifacts := do
  let result ← (Stock.lower function).toOption
  let prepared ← (prepare (Stock.Arithmetic.stage cleanup result.code)).toOption
  let allocated := spillAlloc prepared
  let physical ← (lowerRFunc prepared allocated).toOption
  let assembly ← (emitFunc 0 physical).toOption
  let binary ← assembly.layout.toOption
  if prepCheck (Stock.Arithmetic.stage cleanup result.code) prepared &&
      (checkAlloc prepared allocated).isOk then
    some ⟨result,prepared,allocated,physical,assembly,binary⟩
  else none

private theorem compile_observed : [false,true].all (fun cleanup => (mixed_compile cleanup).isSome) = true := by
  native_decide

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

/-- Both actual modes compile the original complete function to checked machine code. -/
theorem mixed_complete_compilation (cleanup : Bool) :
    ∃ (result : Stock.Result) (prepared : VCode) (allocated : RFunc)
      (physical : AFunc) (assembly : FnAsm) (binary : FnBin),
      CompiledStockArithmeticStage function cleanup 0 result prepared allocated physical assembly binary := by
  have member : cleanup ∈ [false,true] := by cases cleanup <;> simp
  have observed := List.all_eq_true.mp compile_observed cleanup member
  obtain ⟨artifact,run⟩ := Option.isSome_iff_exists.mp observed
  unfold mixed_compile at run
  simp only [Option.bind_eq_some_iff] at run
  obtain ⟨result,lowered,prepared,preparation,physical,allocated,assembly,emitted,binary,layout,last⟩ := run
  split at last
  · rename_i checked
    simp only [Bool.and_eq_true] at checked
    exact ⟨result,prepared,spillAlloc prepared,physical,assembly,binary,
      except_of_toOption lowered,except_of_toOption preparation,checked.1,unit_of_isOk checked.2,
      except_of_toOption allocated,except_of_toOption emitted,except_of_toOption layout⟩
  · cases last

end Backend.Stock.Proof.FenceFixture
