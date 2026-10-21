import FV.Backend.StockScalarCheck
import FV.Backend.Proof.StockLogicalCheck
import FV.Backend.Proof.StockScalarConstantDomain

namespace Backend.Stock.Scalar
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

private theorem normal_abi {params : List Clif.AbiParam} (all : params.all abiEligible = true) :
    ∀ p ∈ params, p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [abiEligible,Arithmetic.abiEligible, Bool.and_eq_true] at good
  have purpose : (p.purpose == .normal) = true := good.1
  exact beq_iff_eq.mp purpose

/-- The current scalar syntax is derived by the runtime classifier. -/
theorem bodyEligible_sound {stm : Clif.Stmt} (checked : bodyEligible stm = true) :
    Stock.Proof.ConstantBody.Family stm.inst := by
  simp only [bodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | constant
  · exact Or.inl (Logical.bodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [constantEligible,inst] at constant
    all_goals try contradiction
    next ty imm => exact Or.inr ⟨ty,imm,rfl⟩

theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : Domain f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  unfold Scalar.eligible at eligible
  split at eligible
  next b blocks =>
    simp only [Bool.and_eq_true] at eligible
    obtain ⟨⟨⟨body,terminal⟩,params⟩,returns⟩ := eligible
    have sourceShape : ∃ xs, b.term = .ret xs := by
      cases term : b.term <;> simp_all
    obtain ⟨xs,ret⟩ := sourceShape
    have families : ∀ stm ∈ b.body, Stock.Proof.ConstantBody.Family stm.inst := by
      intro stm member
      have supported := List.all_eq_true.mp body stm member
      exact bodyEligible_sound supported
    have noSret : f.sig.params.find? (·.purpose == .sret) = none := by
      apply List.find?_eq_none.mpr
      intro p member
      simp [(normal_abi params) p member]
    have ordinary : (sigRets f.sig).any (·.purpose == .sret) = false := by
      rw [sigRets,noSret]
      apply Bool.eq_false_iff.mpr
      intro any
      obtain ⟨p,member,sret⟩ := List.any_eq_true.mp any
      simpa [(normal_abi returns) p member] using sret
    exact domain_of_constant (lowerScope_of scope) (dominated_of dominated) abi blocks families ret ordinary
  next => cases eligible


theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result, Domain f ∧ Stock.lower f = .ok result ∧ result.code = vc ∧
      result.edgeArgs.all (fun row => row.all (·.isEmpty)) = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run,Bool.and_eq_true,decide_eq_true_eq] at lowered
    exact ⟨result,sourceOk_sound source,rfl,lowered.1,lowered.2⟩
end Backend.Stock.Scalar
