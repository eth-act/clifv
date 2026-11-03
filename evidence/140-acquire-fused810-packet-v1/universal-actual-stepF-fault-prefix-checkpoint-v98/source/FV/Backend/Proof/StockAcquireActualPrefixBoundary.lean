import FV.Backend.Proof.StockAcquireFaultChunk

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- An actual successful prefix reaches its next acquire boundary without executing that faulting acquire. -/
theorem acquire_boundary_of_actual_prefix {vc : VCode} {isem : Backend.Proof.Sem}
    {block : VBlock} (placed : vc.blocks[0]? = some block)
    {prefixCode suffix : List MInst} {ty : CTy} {dest pointerReg : Nat} {flags : Clif.MemFlags}
    (pieces : block.insts.toList = prefixCode++(.loadAcquire ty (.vreg dest .int) (.vreg pointerReg .int) flags)::suffix)
    {initialRegs regs : Nat → CV} {initialWorld world : Arm.ArmState}
    (executed : seqRun isem prefixCode initialRegs initialWorld = some (.fall regs world))
    {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat}
    (access : AcquireAt (.loadAcquire ty (.vreg dest .int) (.vreg pointerReg .int) flags) [regs pointerReg] world code address bytes)
    {property : BitVec 64 → Nat → Prop} (allowed : property address bytes) :
    VAcquireBoundaryFrom vc isem ⟨0,0,initialRegs,initialWorld⟩ code property := by
  have instruction : block.insts[prefixCode.length]? =
      some (.loadAcquire ty (.vreg dest .int) (.vreg pointerReg .int) flags) := by
    rw [← Array.getElem?_toList,pieces,List.getElem?_append_right (Nat.le_refl _)]
    simp only [Nat.sub_self,List.getElem?_cons_zero]
  have before : SegAt block 0 prefixCode := by
    intro k bounded
    rw [Nat.zero_add,← Array.getElem?_toList,pieces,List.getElem?_append_left bounded,List.getElem?_eq_getElem bounded]
  have room := (Array.getElem?_eq_some_iff.mp instruction).1
  have path := seqRun_fall_star (vc := vc) (sem := isem) placed before (by simpa only [Nat.zero_add] using room) executed
  exact ⟨0,prefixCode.length,regs,world,block,_,_,[regs pointerReg],address,bytes,
    by simpa only [Nat.zero_add] using path,placed,instruction,rfl,rfl,access,allowed⟩

end Backend.Stock.Proof.Acquire810
