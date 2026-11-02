import FV.Backend.StockMemorySretCopyCheck
import FV.Backend.Proof.StockMemorySretCopyClass

namespace Backend.Stock.MemorySretCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- Source-only admission derives the original ABI-aware copy class. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : SretCopy.CfgClass f := by
  simp only [sourceOk,Bool.and_eq_true,and_assoc] at checked
  obtain ⟨shapeOk,scope,dominated,abi,registers⟩ := checked
  have registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin := by
    intro loc member
    have good := List.all_eq_true.mp registers loc member
    cases loc with
    | reg pin => exact ⟨pin,rfl⟩
    | stack off => cases good
  unfold eligible at shapeOk
  split at shapeOk
  next entry middle target blocks =>
    split at shapeOk
    next first second low lf0 base i0 high lf8 otherBase i8 sf0 storedLow destination j0 sf8 storedHigh otherDestination j8 jump0 jump1 ret filtered =>
      simp only [Bool.and_eq_true,and_assoc,beq_iff_eq,decide_eq_true_eq,Option.isNone_iff_eq_none] at shapeOk
      obtain ⟨firstEq,secondEq,baseEq,lowEq,highEq,destinationEq,entryMiddle,entryTarget,middleTarget,
        lowEarlier,highEarlier,baseParameter,destinationParameter,ln0,ln8,sn0,sn8,entryNops,targetNops⟩ := shapeOk
      subst otherBase
      subst storedLow
      subst storedHigh
      subst otherDestination
      have position : ∀ stm j,(stm,j) ∈ MemoryCapturedCopy.nonNops middle → middle.body[j]? = some stm := by
        intro stm j present
        exact List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp present).1
      have loadLow : middle.body[i0]? = some ⟨[low],.load .load .i64 lf0 base 0⟩ := position _ _ (by rw [filtered]; simp)
      have loadHigh : middle.body[i8]? = some ⟨[high],.load .load .i64 lf8 base 8⟩ := position _ _ (by rw [filtered]; simp)
      have storeLow : middle.body[j0]? = some ⟨[],.store .store .i64 sf0 low destination 0⟩ := position _ _ (by rw [filtered]; simp)
      have storeHigh : middle.body[j8]? = some ⟨[],.store .store .i64 sf8 high destination 8⟩ := position _ _ (by rw [filtered]; simp)
      have shape : ∀ j stm,middle.body[j]? = some stm → j = i0 ∨ j = i8 ∨ j = j0 ∨ j = j8 ∨ stm.inst = .nop := by
        intro j stm found
        by_cases nop : stm.inst = .nop
        · exact .inr (.inr (.inr (.inr nop)))
        have present : (stm,j) ∈ MemoryCapturedCopy.nonNops middle :=
          List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr found,by simpa using nop⟩
        rw [filtered] at present
        simp only [List.mem_cons,List.not_mem_nil,or_false] at present
        rcases present with same | same | same | same
        · exact .inl (congrArg Prod.snd same)
        · exact .inr (.inl (congrArg Prod.snd same))
        · exact .inr (.inr (.inl (congrArg Prod.snd same)))
        · exact .inr (.inr (.inr (.inl (congrArg Prod.snd same))))
      refine ⟨lowerScope_of scope,dominated_of dominated,abi,registerOnly,?_⟩
      refine ⟨entry,middle,target,i0,i8,j0,j8,base,destination,low,high,lf0,lf8,sf0,sf8,blocks,
        ?_,?_,ret,entryMiddle,entryTarget,middleTarget,?_,?_,loadLow,loadHigh,storeLow,storeHigh,
        lowEarlier,highEarlier,shape,List.contains_iff_mem.mp baseParameter,
        List.contains_iff_mem.mp destinationParameter,ln0,ln8,sn0,sn8⟩
      · simpa only [firstEq] using jump0
      · simpa only [secondEq] using jump1
      · intro stm member
        exact of_decide_eq_true (List.all_eq_true.mp entryNops stm member)
      · intro stm member
        exact of_decide_eq_true (List.all_eq_true.mp targetNops stm member)
    next => cases shapeOk
  next => cases shapeOk

/-- The checked output retains both its source class and actual Stock provenance. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,SretCopy.CfgClass f ∧ Stock.lower f = .ok result ∧
      result.code = vc ∧ MemoryStoreCfg.effectsOnly vc = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  have family := sourceOk_sound source
  cases run : Stock.lower f with
  | error error => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨equal,effects⟩ := Bool.and_eq_true_iff.mp lowered
    exact ⟨result,family,rfl,of_decide_eq_true equal,effects⟩

end Backend.Stock.MemorySretCopy
