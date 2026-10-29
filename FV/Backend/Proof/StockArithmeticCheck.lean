module

public import FV.Backend.StockArithmeticCheck

@[expose] public section

namespace Backend.Stock.Arithmetic
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

structure Domain (f : Clif.Function) : Prop where
  scope : LowerScope f
  dominated : Dominated f
  abi : sigAbiOk f.sig = true
  shape : ∃ b xs, f.blocks = [b] ∧ b.term = .ret xs ∧
    ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
      stm.inst = .binary (if subtract then .isub else .iadd) ty x y
  ordinary : (sigRets f.sig).any (·.purpose == .sret) = false

private theorem normal_abi {params : List Clif.AbiParam} (all : params.all abiEligible = true) :
    ∀ p ∈ params, p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [abiEligible, Bool.and_eq_true] at good
  have purpose : (p.purpose == .normal) = true := good.1
  exact beq_iff_eq.mp purpose

/-- The runtime source classifier derives all semantic premises internally. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : Domain f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  unfold Arithmetic.eligible at eligible
  split at eligible
  next b blocks =>
    simp only [Bool.and_eq_true] at eligible
    obtain ⟨⟨⟨body,terminal⟩,params⟩,returns⟩ := eligible
    have sourceShape : ∃ xs, b.term = .ret xs := by
      cases term : b.term <;> simp_all
    obtain ⟨xs,ret⟩ := sourceShape
    have families : ∀ stm ∈ b.body, ∃ subtract : Bool, ∃ ty x y,
        stm.inst = .binary (if subtract then .isub else .iadd) ty x y := by
      intro stm member
      have supported := List.all_eq_true.mp body stm member
      cases inst : stm.inst <;> simp only [bodyEligible,inst] at supported
      all_goals try contradiction
      next op ty x y =>
        simp only [Bool.and_eq_true] at supported
        have ops := supported.1
        simp only [Bool.or_eq_true,beq_iff_eq] at ops
        rcases ops with rfl | rfl
        · exact ⟨false,ty,x,y,rfl⟩
        · exact ⟨true,ty,x,y,rfl⟩
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
    exact ⟨lowerScope_of scope,dominated_of dominated,abi,⟨b,xs,blocks,ret,families⟩,ordinary⟩
  next => cases eligible

/-- The new checker adds a proved actual-Stock alternative; it does not change
the old lowerCheck verdict or require Stock/legacy output equality. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    lowerCheck f vc = true ∨ ∃ result, Domain f ∧ Stock.lower f = .ok result ∧
      result.code = vc ∧ result.edgeArgs.all (fun row => row.all (·.isEmpty)) = true := by
  simp only [check,Bool.or_eq_true,Bool.and_eq_true] at checked
  rcases checked with compatible | ⟨source,lowered⟩
  · exact .inl compatible
  · right
    cases run : Stock.lower f with
    | error message => simp [run] at lowered
    | ok result =>
      simp only [run,Bool.and_eq_true,decide_eq_true_eq] at lowered
      exact ⟨result,sourceOk_sound source,rfl,lowered.1,lowered.2⟩

end Backend.Stock.Arithmetic
