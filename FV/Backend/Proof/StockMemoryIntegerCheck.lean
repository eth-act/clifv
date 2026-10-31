import FV.Backend.StockMemoryIntegerCheck
import FV.Backend.Proof.StockMemoryIntegerClass

namespace Backend.Stock.MemoryUnsigned
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory.IntegerRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The source checker derives a proved unsigned class from original syntax. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) :
    ∃ width,SingleClass width f := by
  simp only [sourceOk,Bool.and_eq_true,Bool.not_eq_true'] at checked
  obtain ⟨⟨⟨⟨⟨shapeOk,scope⟩,dominated⟩,abi⟩,ordinary⟩,registers⟩ := checked
  have registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin := by
    intro loc member
    have good := List.all_eq_true.mp registers loc member
    cases loc with
    | reg pin => exact ⟨pin,rfl⟩
    | stack off => cases good
  unfold eligible at shapeOk
  split at shapeOk
  next b blocks =>
    split at shapeOk
    next z ty flags x body =>
      split at shapeOk
      next ret terminal =>
        simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at shapeOk
        obtain ⟨types,⟨⟨same,parameter⟩,notrap⟩⟩ := shapeOk
        subst ret
        have make (width : Width) (typed : ty = width.sourceTy) : SingleClass width f := by
          refine ⟨lowerScope_of scope,dominated_of dominated,abi,ordinary,registerOnly,?_⟩
          exact ⟨b,x,z,flags,blocks,by simpa only [typed] using body,terminal,
            List.contains_iff_mem.mp parameter,Option.isNone_iff_eq_none.mp notrap⟩
        rcases types with (h8 | h16) | h64
        · exact ⟨.w8,make .w8 h8⟩
        · exact ⟨.w16,make .w16 h16⟩
        · exact ⟨.w64,make .w64 h64⟩
      next => cases shapeOk
    next => cases shapeOk
  next => cases shapeOk

/-- The checked code comes from the proved original source class and actual run. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ width result,SingleClass width f ∧ Stock.lower f = .ok result ∧
      result.code = vc ∧ Memory.effectsOnly vc = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  obtain ⟨width,family⟩ := sourceOk_sound source
  cases run : Stock.lower f with
  | error error => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨equal,effects⟩ := Bool.and_eq_true_iff.mp lowered
    exact ⟨width,result,family,rfl,of_decide_eq_true equal,effects⟩

end Backend.Stock.MemoryUnsigned
