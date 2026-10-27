import FV.Backend.Proof.StockConditionalEmission
import FV.Backend.Proof.StockConditionalValuesWitness

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64

/-- Exact branch-fragment derivation is inhabited by the complete original
source driver, actual descriptor execution and real side-effect emitter. -/
theorem emission_witness : ∃ (f : Clif.Function) (result : Result) (raw descriptor out : V)
    (middle next : State) (trace final : Array RuleId) (code : List MInst),
    Stock.lower f = .ok result ∧ LowerScope f ∧ Dominated f ∧
    ApplyInternal program (Stock.sem result.ctx) {} 199 46 722
      [raw,.label 2,.label 1] (result.initial,#[]) descriptor (middle,trace) ∧
    ApplyInternal program (Stock.sem result.ctx) {} 199 13 242
      [descriptor] (middle,trace) out (next,final) ∧
    BranchCode 2 1 raw code ∧ Frag result.initial.base next.base code := by
  obtain ⟨f,result,descriptor,out,middle,next,trace,final,run,scope,dominated,
    construct,emit,_,_,_⟩ := descriptor_emitter_witness
  have shape : CondShape (.data 123 1 [.reg (.vreg 192 .int),.data 93 1 []]) (fun _ => True) :=
    Or.inr (Or.inl ⟨192,1,OperandSize.size64,rfl,rfl,trivial⟩)
  obtain ⟨code,decoded,fragment⟩ := descriptor_emits rfl (by decide) (by decide) shape construct emit
  exact ⟨f,result,_,descriptor,out,middle,next,trace,final,code,run,scope,dominated,construct,emit,decoded,fragment⟩

end Backend.Stock.Proof.ConditionalValues
