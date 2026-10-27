import FV.Backend.StockMemoryCheck
import FV.Backend.Proof.StockMemoryClass

namespace Backend.Stock.Memory
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original checked shapeOk supplies the complete first memory source class. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : SingleClass f := by
  simp only [sourceOk,Bool.and_eq_true,Bool.not_eq_true'] at checked
  obtain ⟨⟨⟨⟨⟨shapeOk,scope⟩,dominated⟩,abi⟩,ordinary⟩,registers⟩ := checked
  refine ⟨lowerScope_of scope,dominated_of dominated,abi,ordinary,?_,?_⟩
  · intro loc member
    have good := List.all_eq_true.mp registers loc member
    cases loc with
    | reg pin => exact ⟨pin,rfl⟩
    | stack off => cases good
  · unfold eligible at shapeOk
    split at shapeOk
    next b blocks =>
      split at shapeOk
      next z flags x body =>
        split at shapeOk
        next ret terminal =>
          simp only [Bool.and_eq_true,beq_iff_eq] at shapeOk
          obtain ⟨⟨same,parameter⟩,notrap⟩ := shapeOk
          subst ret
          exact ⟨b,x,z,flags,blocks,body,terminal,List.contains_iff_mem.mp parameter,
            Option.isNone_iff_eq_none.mp notrap⟩
        next => cases shapeOk
      next => cases shapeOk
    next => cases shapeOk

/-- The first checked emitted class contains no TLS helper. -/
theorem effectsOnly_noTls {vc : VCode} (checked : effectsOnly vc = true) : vc.hasTls = false := by
  rw [VCode.hasTls,Array.any_eq_false']
  intro vb member
  apply Bool.eq_false_iff.mp
  apply Array.any_eq_false'.mpr
  intro i present
  have blocks := List.all_eq_true.mp checked vb (Array.mem_toList_iff.mpr member)
  have good := List.all_eq_true.mp blocks i (Array.mem_toList_iff.mpr present)
  cases i <;> simp_all [effectInstruction]

/-- The executable checker binds source classification to the actual Stock
artifact; its internal effect check is derived, never supplied by an input. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,SingleClass f ∧ Stock.lower f = .ok result ∧ result.code = vc ∧ effectsOnly vc = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  cases run : Stock.lower f with
  | error error => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨equal,effects⟩ := Bool.and_eq_true_iff.mp lowered
    exact ⟨result,sourceOk_sound source,rfl,of_decide_eq_true equal,effects⟩

end Backend.Stock.Memory
