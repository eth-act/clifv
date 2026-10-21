import FV.Backend.StockScalarCheck
import FV.Backend.Proof.StockLogicalCheck
import FV.Backend.Proof.StockScalarConstantDomain
import FV.Backend.Proof.StockScalarBnotDomain
import FV.Backend.Proof.StockScalarMulDomain
import FV.Backend.Proof.StockScalarShiftDomain
import FV.Backend.Proof.StockScalarCastDomain
import FV.Backend.Proof.StockScalarBitDomain

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

/-- The extended classifier derives original NOT syntax; it adds no root premise. -/
theorem extendedBodyEligible_sound {stm : Clif.Stmt} (checked : extendedBodyEligible stm = true) :
    Stock.Proof.BnotBody.Family stm.inst := by
  simp only [extendedBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | inverted
  · exact Or.inl (bodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [notEligible,inst] at inverted
    all_goals try contradiction
    next op ty x =>
      cases op <;> simp only [notEligible] at inverted
      all_goals try contradiction
      exact Or.inr ⟨ty,x,rfl⟩

theorem mulBodyEligible_sound {stm : Clif.Stmt} (checked : mulBodyEligible stm = true) :
    Stock.Proof.MulBody.Family stm.inst := by
  simp only [mulBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | multiply
  · exact Or.inl (extendedBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [mulEligible,inst] at multiply
    all_goals try contradiction
    next op ty x y =>
      cases op <;> simp only [mulEligible] at multiply
      all_goals try contradiction
      exact Or.inr ⟨ty,x,y,rfl⟩

/-- The shift classifier derives original syntax and keeps selection internal. -/
theorem shiftBodyEligible_sound {stm : Clif.Stmt} (checked : shiftBodyEligible stm = true) :
    Stock.Proof.ShiftBody.Family stm.inst := by
  simp only [shiftBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | shift
  · exact Or.inl (mulBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [shiftEligible,inst] at shift
    all_goals try contradiction
    next op ty x y =>
      cases op <;> simp only [shiftEligible] at shift
      all_goals try contradiction
      · exact Or.inr ⟨.lsl,ty,x,y,rfl⟩
      · exact Or.inr ⟨.lsr,ty,x,y,rfl⟩
      · exact Or.inr ⟨.asr,ty,x,y,rfl⟩

/-- Cast syntax is checked on the original statements, independently of selected roots. -/
theorem castBodyEligible_sound {stm : Clif.Stmt} (checked : castBodyEligible stm = true) :
    Stock.Proof.CastBody.Family stm.inst := by
  simp only [castBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | cast
  · exact Or.inl (shiftBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [castEligible,inst] at cast
    all_goals try contradiction
    · exact Or.inr (Or.inl ⟨_,_,_,rfl⟩)
    · exact Or.inr (Or.inr ⟨_,_,rfl⟩)

/-- The original source classifier derives bit/rotate syntax; no selected root is a premise. -/
theorem bitBodyEligible_sound {stm : Clif.Stmt} (checked : bitBodyEligible stm = true) :
    Stock.Proof.BitBody.Family stm.inst := by
  simp only [bitBodyEligible,Bool.or_eq_true] at checked
  rcases checked with old | bit
  · exact Or.inl (castBodyEligible_sound old)
  · cases inst : stm.inst <;> simp only [bitEligible,inst] at bit
    all_goals try contradiction
    next op ty x =>
      cases op <;> simp only [bitEligible] at bit
      all_goals try contradiction
      all_goals exact Or.inr (Or.inl ⟨_,_,_,by simp [Stock.Proof.BitBody.Unary],rfl⟩)
    next op ty x y =>
      cases op <;> simp only [bitEligible] at bit
      all_goals try contradiction
      all_goals first
        | exact Or.inr (Or.inr ⟨true,_,_,_,rfl⟩)
        | exact Or.inr (Or.inr ⟨false,_,_,_,rfl⟩)

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
    have families : ∀ stm ∈ b.body, Stock.Proof.BitBody.Family stm.inst := by
      intro stm member
      have supported := List.all_eq_true.mp body stm member
      exact bitBodyEligible_sound supported
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
    exact domain_of_bit (lowerScope_of scope) (dominated_of dominated) abi blocks families ret ordinary
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
