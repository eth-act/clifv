import FV.Backend.StockMemoryExtLoadCheck
import FV.Backend.Proof.StockMemoryExtLoadClass

namespace Backend.Stock.MemoryExtending
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory.ExtendedRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The source checker derives a proved extending-load class from original syntax. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) :
    ∃ kind ty,SingleClass kind ty f := by
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
    next z op ty flags x body =>
      split at shapeOk
      next ret terminal =>
        simp only [Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at shapeOk
        obtain ⟨extended,⟨⟨same,parameter⟩,notrap⟩⟩ := shapeOk
        subst ret
        have make (kind : Kind) (opcode : op = kind.sourceOp) : SingleClass kind ty f := by
          refine ⟨lowerScope_of scope,dominated_of dominated,abi,ordinary,registerOnly,?_⟩
          exact ⟨b,x,z,flags,blocks,by simpa only [opcode] using body,terminal,
            List.contains_iff_mem.mp parameter,Option.isNone_iff_eq_none.mp notrap⟩
        cases op with
        | load => cases extended
        | uload8 => exact ⟨.unsigned8,ty,make .unsigned8 rfl⟩
        | sload8 => exact ⟨.signed8,ty,make .signed8 rfl⟩
        | uload16 => exact ⟨.unsigned16,ty,make .unsigned16 rfl⟩
        | sload16 => exact ⟨.signed16,ty,make .signed16 rfl⟩
        | uload32 => exact ⟨.unsigned32,ty,make .unsigned32 rfl⟩
        | sload32 => exact ⟨.signed32,ty,make .signed32 rfl⟩
      next => cases shapeOk
    next => cases shapeOk
  next => cases shapeOk

/-- The checked code comes from the proved original source class and actual run. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ kind ty result,SingleClass kind ty f ∧ Stock.lower f = .ok result ∧
      result.code = vc ∧ Memory.effectsOnly vc = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  obtain ⟨kind,ty,family⟩ := sourceOk_sound source
  cases run : Stock.lower f with
  | error error => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨equal,effects⟩ := Bool.and_eq_true_iff.mp lowered
    exact ⟨kind,ty,result,family,rfl,of_decide_eq_true equal,effects⟩

end Backend.Stock.MemoryExtending
