module

public import FV.Backend.Proof.StockConditionalValues
public import FV.Backend.Proof.StockConditionalTargetsWitness

@[expose] public section

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

private def wideCondition : V := .data 123 1 [.reg (.vreg 192 .int),.data 93 1 []]

/-- A complete original conditional driver supplies the real descriptor and
emitter executions. They inhabit both exact descriptor and emitter projection
bridges without supplying a source-value or emitted-code certificate. -/
theorem descriptor_emitter_witness :
    ∃ (f : Clif.Function) (result : Result) (descriptor out : V) (middle next : State)
      (trace final : Array RuleId),
      Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
      ApplyInternal program (Stock.sem result.ctx) {} 199 46 722
        [wideCondition,.label 2,.label 1] (result.initial,#[]) descriptor (middle,trace) ∧
      ApplyInternal program (Stock.sem result.ctx) {} 199 13 242
        [descriptor] (middle,trace) out (next,final) ∧
      middle.base = result.initial.base ∧ descriptor = brCondV wideCondition 2 1 ∧
      ApplyInternal program (Backend.sem result.ctx) {} 199 13 242
        [descriptor] (middle.base,trace) out (next.base,final) := by
  obtain ⟨result,descriptor,out,middle,next,trace,final,condition,last,run,scope,dominated,
    construct,emit,_,_,_,_⟩ := ConditionalTargetsWitness.stock_conditional_targets_witness ⟨1,by decide⟩
  have actual : ApplyInternal program (Stock.sem result.ctx) {} 199 46 722
      [wideCondition,.label 2,.label 1] (result.initial,#[]) descriptor (middle,trace) := construct
  have emitter : ApplyInternal program (Stock.sem result.ctx) {} 199 13 242
      [descriptor] (middle,trace) out (next,final) := emit
  have shape : CondShape wideCondition (fun _ => True) :=
    Or.inr (Or.inl ⟨192,1,OperandSize.size64,rfl,rfl,trivial⟩)
  obtain ⟨base,descriptorEq⟩ := descriptor_shape rfl (by decide) shape actual
  have projected := BranchHelpers.stock_emit_side_effect_projects result.ctx {} rfl 200 [descriptor] middle trace
  have legacy : ApplyInternal program (Backend.sem result.ctx) {} 199 13 242
      [descriptor] (middle.base,trace) out (next.base,final) := by
    unfold ApplyInternal at emitter ⊢
    rw [emitter] at projected
    exact projected.symm
  exact ⟨_,result,descriptor,out,middle,next,trace,final,run,scope,dominated,actual,
    emitter,base,descriptorEq,legacy⟩

end Backend.Stock.Proof.ConditionalValues
