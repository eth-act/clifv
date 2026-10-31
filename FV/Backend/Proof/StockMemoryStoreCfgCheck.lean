import FV.Backend.StockMemoryStoreCfgCheck
import FV.Backend.Proof.StockMemoryStoreCfgClass

namespace Backend.Stock.MemoryStoreCfg
open Backend.Proof Backend.Proof.Driver Backend.Stock.Proof Backend.Stock.Memory.StoreRoots
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 20000

/-- The source selector derives the complete proved store class internally. -/
theorem sourceOk_sound {f : Clif.Function} (checked : sourceOk f = true) :
    ∃ kind ty,CfgClass kind ty f := by
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
  next entry target blocks =>
    split at shapeOk
    next dst jump terminal =>
      simp only [Bool.and_eq_true] at shapeOk
      obtain ⟨⟨destination,nops⟩,candidates⟩ := shapeOk
      have destinationEq : dst = target.id := by simpa only [beq_iff_eq] using destination
      have entryNops : ∀ stm ∈ entry.body,stm.inst = .nop := by
        intro stm member
        exact of_decide_eq_true (List.all_eq_true.mp nops stm member)
      obtain ⟨⟨stm,storeIndex⟩,present,selected⟩ := List.any_eq_true.mp candidates
      have statement := List.mem_zipIdx_iff_getElem?.mp present
      unfold candidate at selected
      split at selected
      next op ty flags value pointer source =>
        have sourceStmt : stm = ⟨[],.store op ty flags value pointer 0⟩ := source
        simp only [Bool.and_eq_true] at selected
        obtain ⟨⟨⟨parameter,valueParameter⟩,notrap⟩,others⟩ := selected
        obtain ⟨⟨x,valueTy⟩,member,positive⟩ := List.any_eq_true.mp valueParameter
        obtain ⟨same,scalar⟩ := Bool.and_eq_true_iff.mp positive
        have equal : x = value := by simpa only [beq_iff_eq] using same
        subst x
        have shape : ∀ j other,target.body[j]? = some other → j = storeIndex ∨ other.inst = .nop := by
          intro j other found
          have checked := List.all_eq_true.mp others (other,j) (List.mem_zipIdx_iff_getElem?.mpr found)
          simpa only [Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq] using checked
        have make (kind : Memory.StoreRoots.Kind) (opcode : op = kind.sourceOp)
            (width : kind.sourceOp = .store → CTy.ofClif valueTy = .int kind.width.bits) :
            CfgClass kind ty f := by
          refine ⟨lowerScope_of scope,dominated_of dominated,abi,ordinary,registerOnly,?_⟩
          exact ⟨entry,target,storeIndex,value,pointer,flags,valueTy,blocks,entryNops,
            by simpa only [destinationEq] using jump,
            by simpa only [sourceStmt,opcode] using statement,shape,terminal,
            List.contains_iff_mem.mp parameter,member,width,Option.isNone_iff_eq_none.mp notrap⟩
        cases op with
        | store =>
          cases valueTy <;> simp only [MemoryStore.scalarParameter] at scalar
          all_goals first
            | exact ⟨.plain8,ty,make .plain8 rfl (by intro h; rfl)⟩
            | exact ⟨.plain16,ty,make .plain16 rfl (by intro h; rfl)⟩
            | exact ⟨.plain32,ty,make .plain32 rfl (by intro h; rfl)⟩
            | exact ⟨.plain64,ty,make .plain64 rfl (by intro h; rfl)⟩
            | cases scalar
        | istore8 => exact ⟨.narrow8,ty,make .narrow8 rfl (by intro h; cases h)⟩
        | istore16 => exact ⟨.narrow16,ty,make .narrow16 rfl (by intro h; cases h)⟩
        | istore32 => exact ⟨.narrow32,ty,make .narrow32 rfl (by intro h; cases h)⟩
      next => cases selected
    next => cases shapeOk
  next => cases shapeOk

/-- The checked artifact comes from the proved store class and actual driver run. -/
theorem check_sound {f : Clif.Function} {vc : VCode} (checked : check f vc = true) :
    ∃ kind ty result,CfgClass kind ty f ∧ Stock.lower f = .ok result ∧
      result.code = vc ∧ effectsOnly vc = true := by
  simp only [check,Bool.and_eq_true] at checked
  obtain ⟨source,lowered⟩ := checked
  obtain ⟨kind,ty,family⟩ := sourceOk_sound source
  cases run : Stock.lower f with
  | error error => rw [run] at lowered; cases lowered
  | ok result =>
    rw [run] at lowered
    obtain ⟨equal,effects⟩ := Bool.and_eq_true_iff.mp lowered
    exact ⟨kind,ty,result,family,rfl,of_decide_eq_true equal,effects⟩

end Backend.Stock.MemoryStoreCfg
