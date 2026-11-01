import FV.Backend.StockMemoryCapturedCopyCheck
import FV.Backend.Proof.StockMemoryCapturedCopyClass

namespace Backend.Stock.MemoryCapturedCopy
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The selector derives the complete class from original source positions. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) : CapturedCopy.CfgClass f := by
  simp only [sourceOk,Bool.and_eq_true,Bool.not_eq_true',and_assoc] at checked
  obtain ⟨shapeOk,scope,dominated,abi,ordinary,registers⟩ := checked
  have registerOnly : ∀ loc ∈ locsOf f.sig,∃ pin,loc = .reg pin := by
    intro loc member
    have good := List.all_eq_true.mp registers loc member
    cases loc with
    | reg pin => exact ⟨pin,rfl⟩
    | stack off => cases good
  unfold eligible at shapeOk
  split at shapeOk
  next entry target blocks =>
    split at shapeOk
    next dst value vf base iv pointer pf otherBase ip sf stored destination is jump ret filtered =>
      simp only [Bool.and_eq_true,and_assoc,beq_iff_eq,decide_eq_true_eq,Option.isNone_iff_eq_none] at shapeOk
      obtain ⟨dstEq,baseEq,valueEq,pointerEq,valueEarlier,pointerEarlier,parameter,vn,pn,sn,nops⟩ := shapeOk
      subst otherBase
      subst stored
      subst destination
      have entryNops : ∀ stm ∈ entry.body,stm.inst = .nop := by
        intro stm member
        exact of_decide_eq_true (List.all_eq_true.mp nops stm member)
      have position : ∀ stm j,(stm,j) ∈ nonNops target → target.body[j]? = some stm := by
        intro stm j present
        exact List.mem_zipIdx_iff_getElem?.mp (List.mem_filter.mp present).1
      have valueStatement : target.body[iv]? = some ⟨[value],.load .load .i64 vf base 8⟩ :=
        position _ _ (by rw [filtered]; simp)
      have pointerStatement : target.body[ip]? = some ⟨[pointer],.load .load .i64 pf base 0⟩ :=
        position _ _ (by rw [filtered]; simp)
      have storeStatement : target.body[is]? = some ⟨[],.store .store .i64 sf value pointer 0⟩ :=
        position _ _ (by rw [filtered]; simp)
      have shape : ∀ j stm,target.body[j]? = some stm → j = iv ∨ j = ip ∨ j = is ∨ stm.inst = .nop := by
        intro j stm found
        by_cases nop : stm.inst = .nop
        · exact .inr (.inr (.inr nop))
        have present : (stm,j) ∈ nonNops target :=
          List.mem_filter.mpr ⟨List.mem_zipIdx_iff_getElem?.mpr found,by simpa using nop⟩
        rw [filtered] at present
        simp only [List.mem_cons,List.not_mem_nil,or_false] at present
        rcases present with same | same | same
        · exact .inl (congrArg Prod.snd same)
        · exact .inr (.inl (congrArg Prod.snd same))
        · exact .inr (.inr (.inl (congrArg Prod.snd same)))
      refine ⟨lowerScope_of scope,dominated_of dominated,abi,ordinary,registerOnly,?_⟩
      exact ⟨entry,target,iv,ip,is,base,value,pointer,vf,pf,sf,blocks,entryNops,
        by simpa only [dstEq] using jump,valueStatement,pointerStatement,storeStatement,
        valueEarlier,pointerEarlier,shape,ret,List.contains_iff_mem.mp parameter,vn,pn,sn⟩
    next => cases shapeOk
  next => cases shapeOk

/-- The checked artifact has complete source correctness and actual Stock provenance. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ result,CapturedCopy.CfgClass f ∧ Stock.lower f = .ok result ∧
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

end Backend.Stock.MemoryCapturedCopy
