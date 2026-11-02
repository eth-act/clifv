import FV.Backend.Proof.StockAcquireAllocatedLine

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The acquire boundary retains the exact source address operand. -/
theorem AcquireAt.load_inv {ty : CTy} {d pointer : Reg} {flags : Clif.MemFlags}
    {uses : List CV} {world : Arm.ArmState} {code : Clif.TrapCode}
    {address : BitVec 64} {bytes : Nat}
    (access : AcquireAt (.loadAcquire ty d pointer flags) uses world code address bytes) :
    ∃ value,uses = [value] ∧ address = lo64 value ∧ bytes = ty.bytes ∧
      AtomTy ty ∧ flags.trapCode = some code := by
  cases access with
  | acquire atomic flag => exact ⟨_,rfl,rfl,rfl,atomic,flag⟩

/-- The checked byte acquire faults at its actual physical operand and original trap code. -/
theorem acquire_byte_fault_site {R : RL} (wellFormed : R.Wf) {s : Arm.ArmState}
    {b k d pointer : Nat} {allocs : Array Loc} {items : List RItem}
    {values : Loc → CV} {world : Arm.ArmState} {block : VBlock} {flags : Clif.MemFlags}
    (related : Q R s (.run ⟨b,.op k allocs :: items,values,world⟩))
    (found : R.vc.blocks[b]? = some block)
    (located : block.insts[k]? = some (.loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags))
    {operands : Array Operand}
    (valid : (MInst.loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags).operands = .ok operands)
    {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat} {mp : ArmFault.MemMap}
    (access : AcquireAt (.loadAcquire (.int 8) (.vreg d .int) (.vreg pointer .int) flags)
      (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world code address bytes)
    (unmapped : ∃ j < bytes,mp (address + BitVec.ofNat 64 j) = .none) :
    TrapAtF mp R.fb R.base code s := by
  obtain ⟨value,sourceUses,rfl,rfl,atomic,flag⟩ := access.load_inv
  obtain ⟨j,destination,base,destinationBound,baseBound,line,pc,clean,program,uses⟩ :=
    acquire_byte_line related found located
  have valueEq : value = regVal s (.x base) :=
    (List.cons.inj (sourceUses.symm.trans (uses operands valid))).1
  obtain ⟨byte,bound,missing⟩ := unmapped
  have byteZero : byte = 0 := by simp only [CTy.bytes,CTy.bits] at bound; omega
  subst byte
  rw [valueEq,lo64_regVal_x] at missing
  have marked : R.L[j]? = some (.ins (.ldar 8 (.x destination) (.x base)) (some code)) := by
    simpa only [flag] using line
  apply acquire_byte_line_fault wellFormed (by omega : base ≤ 30) (by omega : destination ≤ 30)
    marked pc clean program
  simpa [Arm.read_gpr,rnum] using missing

end Backend.Stock.Proof.Acquire810
