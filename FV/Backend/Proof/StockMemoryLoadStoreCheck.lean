import FV.Backend.StockMemoryLoadStoreCheck
import FV.Backend.Proof.StockMemoryLoadStoreClass

namespace Backend.Stock.MemoryLoadStore
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Original source selection derives the complete mixed memory class internally. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) :
    ∃ width kind ty,LoadStore.SingleClass width kind ty f := by
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
    next z loadTy loadFlags loadPointer op ty storeFlags value storePointer body =>
      split at shapeOk
      next returned terminal =>
        simp only [Bool.and_eq_true] at shapeOk
        obtain ⟨⟨⟨⟨⟨⟨resultEq,loadScalar⟩,loadParameter⟩,storeParameter⟩,valueParameter⟩,loadNotrap⟩,storeNotrap⟩ := shapeOk
        have sameResult : z = returned := by simpa only [beq_iff_eq] using resultEq
        subst returned
        obtain ⟨⟨x,valueTy⟩,member,positive⟩ := List.any_eq_true.mp valueParameter
        obtain ⟨same,scalar⟩ := Bool.and_eq_true_iff.mp positive
        have equal : x = value := by simpa only [beq_iff_eq] using same
        subst x
        have make (width : IntegerRoots.Width) (loadWidth : loadTy = width.sourceTy)
            (kind : StoreRoots.Kind) (opcode : op = kind.sourceOp)
            (storeWidth : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) :
            LoadStore.SingleClass width kind ty f := by
          refine ⟨lowerScope_of scope,dominated_of dominated,abi,ordinary,registerOnly,?_⟩
          exact ⟨b,loadPointer,storePointer,value,z,loadFlags,storeFlags,valueTy,blocks,
            by simpa only [loadWidth,opcode] using body,terminal,
            List.contains_iff_mem.mp loadParameter,List.contains_iff_mem.mp storeParameter,
            member,storeWidth,Option.isNone_iff_eq_none.mp loadNotrap,
            Option.isNone_iff_eq_none.mp storeNotrap⟩
        have chooseStore (width : IntegerRoots.Width) (loadWidth : loadTy = width.sourceTy) :
            ∃ kind,LoadStore.SingleClass width kind ty f := by
          cases op with
          | store =>
            cases valueTy <;> simp only [MemoryStore.scalarParameter] at scalar
            all_goals first
              | exact ⟨.plain8,make width loadWidth .plain8 rfl (by intro h; rfl)⟩
              | exact ⟨.plain16,make width loadWidth .plain16 rfl (by intro h; rfl)⟩
              | exact ⟨.plain32,make width loadWidth .plain32 rfl (by intro h; rfl)⟩
              | exact ⟨.plain64,make width loadWidth .plain64 rfl (by intro h; rfl)⟩
              | cases scalar
          | istore8 => exact ⟨.narrow8,make width loadWidth .narrow8 rfl (by intro h; cases h)⟩
          | istore16 => exact ⟨.narrow16,make width loadWidth .narrow16 rfl (by intro h; cases h)⟩
          | istore32 => exact ⟨.narrow32,make width loadWidth .narrow32 rfl (by intro h; cases h)⟩
        cases loadTy with
        | i8 => obtain ⟨kind,family⟩ := chooseStore .w8 rfl; exact ⟨.w8,kind,ty,family⟩
        | i16 => obtain ⟨kind,family⟩ := chooseStore .w16 rfl; exact ⟨.w16,kind,ty,family⟩
        | i32 => obtain ⟨kind,family⟩ := chooseStore .w32 rfl; exact ⟨.w32,kind,ty,family⟩
        | i64 => obtain ⟨kind,family⟩ := chooseStore .w64 rfl; exact ⟨.w64,kind,ty,family⟩
        | _ => cases loadScalar
      next => cases shapeOk
    next => cases shapeOk
  next => cases shapeOk

/-- The checked artifact comes from its original source class and actual driver execution. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ width kind ty result,LoadStore.SingleClass width kind ty f ∧ Stock.lower f = .ok result ∧
      result.code = vc ∧ Memory.Store.effectsOnly vc = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  obtain ⟨width,kind,ty,family⟩ := sourceOk_sound source
  cases run : Stock.lower f with
  | error error => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨equal,effects⟩ := Bool.and_eq_true_iff.mp lowered
    exact ⟨width,kind,ty,result,family,rfl,of_decide_eq_true equal,effects⟩

end Backend.Stock.MemoryLoadStore
