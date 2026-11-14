import FV.Backend.StockMemorySinkSourceCheck
import FV.Backend.Proof.StockMemorySinkExtCheck

/-! Soundness of the executable selector and check of the sinking load/extension class for
a plain or an atomic source load: the checked source is a `SourceExtClass`, whose contract is
`Stock.Memory.ExplicitDomain` (`SourceExtClass.domain`). -/
namespace Backend.Stock.MemorySinkExt
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.SinkExtend
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

private theorem narrowResult_narrow {ty : Clif.Ty} (small : narrowResult ty = true) : narrow ty = true := by
  cases ty <;> simp_all [narrowResult,narrow]

/-- A selected source load is the plain or atomic source of a sinking kind that admits
the extension. -/
theorem sourcePointer_sound {load : Clif.Inst} {op : Clif.ExtendOp} {x : Nat}
    (selected : sourcePointer? load op = some x) :
    ∃ (src : Source) (kind : Kind) (flags : Clif.MemFlags),
      load = src.load (loadTy kind) flags x ∧ extendOp kind = op ∧ src.admits kind = true := by
  unfold sourcePointer? at selected
  split at selected
  next inTy flags pointer =>
    by_cases chosen : kindOf op inTy = true
    · simp only [chosen,↓reduceIte,Option.some.injEq] at selected
      subst selected
      obtain ⟨kind,opEq,tyEq⟩ := kind_of chosen
      subst tyEq
      exact ⟨.plain,kind,flags,rfl,opEq,rfl⟩
    · simp [chosen] at selected
  next inTy flags pointer =>
    by_cases chosen : kindOf .uextend inTy = true
    · simp only [chosen,↓reduceIte,Option.some.injEq] at selected
      subst selected
      obtain ⟨kind,opEq,tyEq⟩ := kind_of chosen
      subst tyEq
      refine ⟨.acquire,kind,flags,rfl,opEq,?_⟩
      revert opEq
      cases kind <;> decide
    · simp [chosen] at selected
  next => cases selected

/-- The general source checker derives the proved sinking class, for a plain or an
atomic source load, from original syntax. -/
theorem sourceOkAny_sound {f : Clif.Function} (checked : sourceOkAny f = true) :
    ∃ src kind ty,SourceExtClass src kind ty f := by
  simp only [sourceOkAny,Bool.and_eq_true,Bool.not_eq_true'] at checked
  obtain ⟨⟨⟨⟨⟨shapeOk,scope⟩,dominated⟩,abi⟩,ordinary⟩,registers⟩ := checked
  have registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin := by
    intro loc member
    have good := List.all_eq_true.mp registers loc member
    cases loc with
    | reg pin => exact ⟨pin,rfl⟩
    | stack off => cases good
  unfold eligibleAny at shapeOk
  split at shapeOk
  next b blocks =>
    split at shapeOk
    next y load z op out operand body =>
      split at shapeOk
      next returned x terminal selected =>
        simp only [Bool.and_eq_true,beq_iff_eq] at shapeOk
        obtain ⟨⟨⟨same,result⟩,small⟩,parameter⟩ := shapeOk
        subst operand returned
        obtain ⟨src,kind,flags,loadEq,opEq,admits⟩ := sourcePointer_sound selected
        subst loadEq opEq
        exact ⟨src,kind,out,lowerScope_of scope,dominated_of dominated,abi,ordinary,registerOnly,
          b,x,y,z,flags,blocks,body,terminal,narrowResult_narrow small,List.contains_iff_mem.mp parameter,
          ordinary,admits⟩
      next => cases shapeOk
    next => cases shapeOk
  next => cases shapeOk

/-- The general check's code comes from the proved original source class and the actual
run, with sinking-class effects. -/
theorem checkAny_sound {f : Clif.Function} {vc : VCode} (checked : checkAny f vc = true) :
    ∃ src kind ty result,SourceExtClass src kind ty f ∧ Stock.lower f = .ok result ∧
      result.code = vc ∧ Memory.sinkEffectsOnly vc = true := by
  simp only [checkAny,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  obtain ⟨src,kind,ty,family⟩ := sourceOkAny_sound source
  cases run : Stock.lower f with
  | error error => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨equal,effects⟩ := Bool.and_eq_true_iff.mp lowered
    exact ⟨src,kind,ty,result,family,rfl,of_decide_eq_true equal,effects⟩

end Backend.Stock.MemorySinkExt
