import FV.Backend.StockMemoryStoreCheck
import FV.Backend.Proof.StockMemoryStoreClass

namespace Backend.Stock.MemoryStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The source selector derives the complete proved store class internally. -/
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
    next op ty flags value pointer body =>
      split at shapeOk
      next terminal =>
        simp only [Bool.and_eq_true] at shapeOk
        obtain ⟨⟨parameter,valueParameter⟩,notrap⟩ := shapeOk
        obtain ⟨⟨x,valueTy⟩,member,positive⟩ := List.any_eq_true.mp valueParameter
        obtain ⟨same,scalar⟩ := Bool.and_eq_true_iff.mp positive
        have equal : x = value := by simpa only [beq_iff_eq] using same
        subst x
        have make (kind : Kind) (opcode : op = kind.sourceOp)
            (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) :
            SingleClass kind ty f := by
          refine ⟨lowerScope_of scope,dominated_of dominated,abi,ordinary,registerOnly,?_⟩
          exact ⟨b,value,pointer,flags,valueTy,blocks,by simpa only [opcode] using body,
            terminal,List.contains_iff_mem.mp parameter,member,width,Option.isNone_iff_eq_none.mp notrap⟩
        cases op with
        | store =>
          cases valueTy <;> simp only [scalarParameter] at scalar
          all_goals first
            | exact ⟨.plain8,ty,make .plain8 rfl (by intro h; rfl)⟩
            | exact ⟨.plain16,ty,make .plain16 rfl (by intro h; rfl)⟩
            | exact ⟨.plain32,ty,make .plain32 rfl (by intro h; rfl)⟩
            | exact ⟨.plain64,ty,make .plain64 rfl (by intro h; rfl)⟩
            | cases scalar
        | istore8 => exact ⟨.narrow8,ty,make .narrow8 rfl (by intro h; cases h)⟩
        | istore16 => exact ⟨.narrow16,ty,make .narrow16 rfl (by intro h; cases h)⟩
        | istore32 => exact ⟨.narrow32,ty,make .narrow32 rfl (by intro h; cases h)⟩
      next => cases shapeOk
    next => cases shapeOk
  next => cases shapeOk

/-- The checked artifact comes from the proved store class and actual driver run. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ kind ty result,SingleClass kind ty f ∧ Stock.lower f = .ok result ∧
      result.code = vc ∧ Memory.Store.effectsOnly vc = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  obtain ⟨kind,ty,family⟩ := sourceOk_sound source
  cases run : Stock.lower f with
  | error error => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨equal,effects⟩ := Bool.and_eq_true_iff.mp lowered
    exact ⟨kind,ty,result,family,rfl,of_decide_eq_true equal,effects⟩

end Backend.Stock.MemoryStore
