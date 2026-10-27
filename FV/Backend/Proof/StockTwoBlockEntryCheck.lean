import FV.Backend.Lowering.StockTwoBlockEntry
import FV.Backend.Proof.StockTwoBlockDomain
import FV.Backend.Proof.StockScalarCheck

namespace Backend.Stock.TwoBlock.Entry
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem entry_family {stm : Clif.Stmt} (checked : entryEligible stm = true) :
    (∃ ty imm,stm.inst = .iconst ty imm) ∨ (∃ op ty x y,stm.inst = .div op ty x y) ∨ stm.inst = .nop := by
  simp only [entryEligible,Bool.and_eq_true] at checked
  have shape := checked.2
  cases inst : stm.inst <;> simp only [inst] at shape <;> try cases shape
  case iconst => exact .inl ⟨_,_,rfl⟩
  case div => exact .inr (.inl ⟨_,_,_,_,rfl⟩)
  case nop => exact .inr (.inr rfl)

private theorem normal_abi {params : List Clif.AbiParam}
    (all : params.all Scalar.narrowAbiEligible = true) : ∀ p ∈ params,p.purpose = .normal := by
  intro p member
  have good := List.all_eq_true.mp all p member
  simp only [Scalar.narrowAbiEligible,Bool.and_eq_true] at good
  exact beq_iff_eq.mp good.1

/-- The executable class predicate derives the existing universal production
contract under the original source/ABI checks. No proof input is requested. -/
theorem domain_of_eligible {f : Clif.Function} (checked : eligible f = true)
    (scope : LowerScope f) (dominated : Dominated f) (abi : sigAbiOk f.sig = true) : Scalar.Domain f := by
  unfold eligible at checked
  split at checked
  next entry target blocks =>
    split at checked
    next bc jump =>
      split at checked
      next xs ret =>
        simp only [Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at checked
        obtain ⟨⟨⟨⟨⟨⟨destination,different⟩,entryBody⟩,targetBody⟩,forwarded⟩,params⟩,returns⟩ := checked
        have entryFamily := fun stm member => Scalar.maskMixedBodyEligible_sound
          (show Scalar.maskMixedBodyEligible stm = true from List.all_eq_true.mp entryBody stm member)
        have family : ∀ b ∈ f.blocks,∀ stm ∈ b.body,MaskBody.Family stm.inst := by
          intro b member stm present
          rw [blocks] at member
          simp only [List.mem_cons,List.not_mem_nil,or_false] at member
          rcases member with rfl | rfl
          · have checked := List.all_eq_true.mp entryBody stm present
            exact Scalar.maskMixedBodyEligible_sound checked
          · exact Scalar.maskMixedBodyEligible_sound (List.all_eq_true.mp targetBody stm present)
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
        exact Scalar.domain_of_two_block_scalar_entry scope dominated abi ordinary blocks jump ret destination different
          family entryFamily (by
            intro stm member x defined
            exact List.contains_iff_mem.mp (List.all_eq_true.mp (List.all_eq_true.mp forwarded stm member) x defined))
      next => cases checked
    next => cases checked
  next => cases checked

theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : Scalar.Domain f := by
  simp only [sourceOk,Bool.and_eq_true] at checked
  obtain ⟨⟨⟨eligible,scope⟩,dominated⟩,abi⟩ := checked
  exact domain_of_eligible eligible (lowerScope_of scope) (dominated_of dominated) abi

theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,Scalar.Domain f ∧ Stock.lower f = .ok result ∧ result.code = vc := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error message => simp [run] at lowered
  | ok result =>
    simp only [run,decide_eq_true_eq] at lowered
    exact ⟨result,sourceOk_sound source,rfl,lowered⟩

end Backend.Stock.TwoBlock.Entry
