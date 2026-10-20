import FV.Backend.Proof.StockCallOutputValues
import FV.Backend.Proof.StockCallStaticWitness
namespace Backend.Stock.Proof.CallOutputValuesWitnessDraft
open Backend.Proof Backend.Proof.Driver Backend.Proof.Spill Backend.Proof.PerEdgePrep Isle Isle.Interp Isle.Aarch64
open Backend.Stock.Proof.CallStaticFixture Backend.Stock.Proof.CallOutputValuesDraft
set_option maxRecDepth 20000
set_option maxHeartbeats 6000000
attribute [local irreducible] Isle.Aarch64.program Stock.runTerm Stock.lower
private def values (implicit : Bool) : List Clif.Val := if implicit then [] else [⟨.i64,7⟩,⟨.i64,9⟩]
private def results (implicit : Bool) : List CV := if implicit then [] else [7,9]
private theorem held (implicit : Bool) : AllHold (values implicit) (results implicit) := by
  cases implicit with
  | false =>
    constructor
    · rfl
    · intro j v x atValue atResult
      rcases j with _ | (_ | j)
      all_goals simp [values,results] at atValue atResult
      all_goals cases atValue; cases atResult; rfl
  | true => exact ⟨rfl,by intro j v x atValue; simp [values] at atValue⟩

/-- Complete original call pipelines exercise result-value transport with real
nonempty ordinary results7/9 (and empty explicit sret results). Result writing
frames every earlier vreg. This witnesses the local call-result contract;
source-callee/world realization and selected-root composition remain required. -/
theorem stock_complete_call_output_values_witness (indirect implicit : Bool) :
    ∃ (out : Output) (vs : List Clif.Val) (xs : List CV),
      LowerScope (function indirect implicit) ∧ Dominated (function indirect implicit) ∧
      ArityOk (function indirect implicit) ∧ sigAbiOk (signature indirect implicit) = true ∧
      Stock.lower (function indirect implicit) = .ok out.result ∧
      prepareAt out.result.code out.result.edgeArgs = .ok out.prepared ∧
      out.rf = spillAllocAt out.prepared.code out.prepared.edges ∧
      checkAllocAt out.prepared.code out.prepared.edges out.rf = .ok () ∧
      lowerRFunc out.prepared.code out.rf = .ok out.af ∧ Facts indirect implicit out ∧
      Stock.externCtor out.result.ctx T.gen_call_output [.op (.sig (signature indirect implicit))] out.result.initial = .ok (out.outs,out.afterOut) ∧
      Stock.externCtor out.result.ctx T.gen_call_rets [.op (.sig (signature indirect implicit)),out.outs] out.afterOut = .ok (out.defs,out.afterPins) ∧
      AllHold vs xs ∧ vs.length = (signature indirect implicit).returns.length ∧
      (implicit = false → vs.length = 2) ∧ (implicit = true → vs = []) ∧
      (∀ (fr : Clif.Frame) (ρ : Nat → CV),
        ResultsHeld out.result.initial.base.nextVreg fr (outRegs out.result.initial.base (signature indirect implicit).returns.length) vs
          (writeV ρ ((callDefOps (outDefs out.result.initial.base.nextVreg (signature indirect implicit).returns.length)).zip xs))) ∧
      ∀ (ρ : Nat → CV) (ys : List CV) (n : Nat),n < out.result.initial.base.nextVreg →
        writeV ρ ((callDefOps (outDefs out.result.initial.base.nextVreg (signature indirect implicit).returns.length)).zip ys) n = ρ n := by
  obtain ⟨out,pipeline,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,facts,
    output,pinned,arguments,info,fresh,static⟩ := CallStaticWitnessDraft.stock_complete_call_static_witness indirect implicit
  have transported := stock_call_output_values output pinned
  have count : (values implicit).length = (signature indirect implicit).returns.length := by cases implicit <;> rfl
  exact ⟨out,values implicit,results implicit,scope,dominated,arity,abi,lowered,prepared,fallback,checked,physical,
    facts,output,pinned,held implicit,count,(by intro flag; subst implicit; rfl),(by intro flag; subst implicit; rfl),
    fun fr ρ => transported.2.2 fr ρ _ _ (held implicit) count,transported.2.1⟩
end Backend.Stock.Proof.CallOutputValuesWitnessDraft
