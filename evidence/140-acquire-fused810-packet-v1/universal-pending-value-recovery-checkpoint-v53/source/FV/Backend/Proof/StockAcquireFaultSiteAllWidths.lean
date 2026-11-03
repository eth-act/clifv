import FV.Backend.Proof.StockAcquireEncodingFaultAllWidths
import FV.Backend.Proof.StockAcquireFaultSite

namespace Backend.Stock.Proof.Acquire810
open Backend Backend.Proof E2E
set_option autoImplicit false
set_option Elab.async false

/-- Every admitted acquire line faults at its original trap entry and exact unmapped byte. -/
theorem acquire_all_widths_line_fault {R : RL} (wellFormed : R.Wf) {s : Arm.ArmState}
    {j base destination width : Nat} {code : Clif.TrapCode}
    (baseReg : base ≤ 30) (destinationReg : destination ≤ 30)
    (widthOk : width = 8 ∨ width = 16 ∨ width = 32 ∨ width = 64)
    (line : R.L[j]? = some (.ins (.ldar width (.x destination) (.x base)) (some code)))
    (pc : Arm.r .PC s = R.pcOf j) (clean : Arm.r .ERR s = .None)
    (program : s.program = R.fb.program R.base) {mp : ArmFault.MemMap}
    (unmapped : ∃ byte < width/8,mp (Arm.read_gpr 64 (BitVec.ofNat 5 base) s+BitVec.ofNat 64 byte) = .none) :
    TrapAtF mp R.fb R.base code s := by
  have trap := MemoryFaults.access_trapAt_ins wellFormed line pc clean
  obtain ⟨inst,encoded,decoded⟩ := MemoryFaults.access_decodeAt_line wellFormed line program pc
  obtain ⟨byte,bound,missing⟩ := unmapped
  exact ⟨trap,(ArmFault.faults_iff (show Arm.read_err s = .None from clean) decoded).mpr
    (encoded_acquire_all_widths_fault baseReg destinationReg widthOk encoded bound missing)⟩

/-- The actual checked acquire faults at its physical operand for all original atomic widths. -/
theorem acquire_all_widths_fault_site {R : RL} (wellFormed : R.Wf) {s : Arm.ArmState}
    {b k d pointer : Nat} {allocs : Array Loc} {items : List RItem}
    {values : Loc → CV} {world : Arm.ArmState} {block : VBlock} {flags : Clif.MemFlags} {ty : CTy}
    (related : Q R s (.run ⟨b,.op k allocs :: items,values,world⟩))
    (found : R.vc.blocks[b]? = some block)
    (located : block.insts[k]? = some (.loadAcquire ty (.vreg d .int) (.vreg pointer .int) flags))
    {operands : Array Operand}
    (valid : (MInst.loadAcquire ty (.vreg d .int) (.vreg pointer .int) flags).operands = .ok operands)
    {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat} {mp : ArmFault.MemMap}
    (access : AcquireAt (.loadAcquire ty (.vreg d .int) (.vreg pointer .int) flags)
      (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world code address bytes)
    (unmapped : ∃ j < bytes,mp (address+BitVec.ofNat 64 j) = .none) :
    TrapAtF mp R.fb R.base code s := by
  obtain ⟨value,sourceUses,rfl,rfl,atomic,flag⟩ := access.load_inv
  obtain ⟨j,destination,base,destinationBound,baseBound,line,pc,clean,program,uses⟩ :=
    acquire_all_widths_line related found located
  have valueEq : value = regVal s (.x base) :=
    (List.cons.inj (sourceUses.symm.trans (uses operands valid))).1
  have widthOk : ty.bits = 8 ∨ ty.bits = 16 ∨ ty.bits = 32 ∨ ty.bits = 64 := by
    rcases atomic with rfl | rfl | rfl | rfl <;> simp [CTy.bits]
  have bytesEq : ty.bytes = ty.bits/8 := by
    rcases atomic with rfl | rfl | rfl | rfl <;> rfl
  have marked : R.L[j]? = some (.ins (.ldar ty.bits (.x destination) (.x base)) (some code)) := by
    simpa only [flag] using line
  apply acquire_all_widths_line_fault wellFormed (by omega : base ≤ 30) (by omega : destination ≤ 30)
    widthOk marked pc clean program
  obtain ⟨byte,bound,missing⟩ := unmapped
  refine ⟨byte,by rwa [← bytesEq],?_⟩
  rw [valueEq,lo64_regVal_x] at missing
  simpa [Arm.read_gpr,rnum] using missing

end Backend.Stock.Proof.Acquire810
