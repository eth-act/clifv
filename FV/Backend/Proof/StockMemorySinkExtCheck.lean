import FV.Backend.StockMemorySinkExtCheck
import FV.E2E.StockMemorySinkExtDomain
import FV.Backend.Proof.LowerDecide

/-! Soundness of the executable selector and check of the sinking load/extension
class. The checked source is a `SinkExtClass`, whose contract is
`Stock.Memory.ExplicitDomain`.

Why `ExplicitDomain` and not the draft `MemoryFaults.DomainWithAccessTraps`
(`StockMemoryFaultContract.lean`): the production theorems already carry the run
premise `TrapsExplicit`, which excludes memory-access traps. The legacy route and the
CallStore family treat faulting accesses this way, and `ExplicitDomain` matches that
treatment with no new machine-fault obligation. A contract with access traps remains
possible later; it would add the machine-side fault refinement of the extending load. -/
namespace Backend.Stock.MemorySinkExt
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof
open Backend.Stock.Memory.SinkExtend
open Backend.Stock.Memory.ExtendedRoots (Kind)
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- A selected extension determines its extending-load kind. -/
theorem kind_of {op : Clif.ExtendOp} {inTy : Clif.Ty} (selected : kindOf op inTy = true) :
    ∃ kind : Kind,extendOp kind = op ∧ loadTy kind = inTy := by
  cases op <;> cases inTy <;> simp [kindOf] at selected
  · exact ⟨.unsigned8,rfl,rfl⟩
  · exact ⟨.unsigned16,rfl,rfl⟩
  · exact ⟨.unsigned32,rfl,rfl⟩
  · exact ⟨.signed8,rfl,rfl⟩
  · exact ⟨.signed16,rfl,rfl⟩
  · exact ⟨.signed32,rfl,rfl⟩

private theorem narrow_of {ty : Clif.Ty} (small : narrowResult ty = true) : narrow ty = true := by
  cases ty <;> simp_all [narrowResult,narrow]

/-- The source checker derives the proved sinking class from original syntax. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) :
    ∃ kind ty,SinkExtClass kind ty f := by
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
    next y inTy flags x z op out operand body =>
      split at shapeOk
      next returned terminal =>
        simp only [Bool.and_eq_true,beq_iff_eq] at shapeOk
        obtain ⟨⟨⟨⟨selected,same⟩,result⟩,small⟩,parameter⟩ := shapeOk
        subst operand returned
        obtain ⟨kind,opEq,tyEq⟩ := kind_of selected
        subst opEq tyEq
        exact ⟨kind,out,lowerScope_of scope,dominated_of dominated,abi,ordinary,registerOnly,
          b,x,y,z,flags,blocks,body,terminal,narrow_of small,List.contains_iff_mem.mp parameter,
          ordinary⟩
      next => cases shapeOk
    next => cases shapeOk
  next => cases shapeOk

/-- The checked code comes from the proved original source class and the actual run. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ kind ty result,SinkExtClass kind ty f ∧ Stock.lower f = .ok result ∧
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

end Backend.Stock.MemorySinkExt
