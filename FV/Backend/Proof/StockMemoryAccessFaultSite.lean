import FV.Backend.Proof.StockMemoryAccessLoadLine
import FV.Backend.Proof.StockMemoryAccessStoreLine
import FV.Backend.Proof.StockMemoryAccessShape
import FV.E2E.MemTrapStatement

namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver E2E
set_option autoImplicit false
set_option Elab.async false

/-- The checked ordinary load reaches the original trap-table code and faults at its actual address. -/
theorem load_unsigned_fault_site {R : RL} (wellFormed : R.Wf) {s : Arm.ArmState}
    {b k d pointer offset sb : Nat} {allocs : Array Loc} {items : List RItem}
    {values : Loc → CV} {world : Arm.ArmState} {block : VBlock} {flags : Clif.MemFlags}
    (related : Q R s (.run ⟨b,.op k allocs :: items,values,world⟩))
    (found : R.vc.blocks[b]? = some block)
    (located : block.insts[k]? = some (.load .uload64 (.vreg d .int)
      (.unsignedOffset (.vreg pointer .int) offset) flags))
    (sourceOffset : offset = 0 ∨ offset = 16) {operands : Array Operand}
    (valid : (MInst.load .uload64 (.vreg d .int) (.unsignedOffset (.vreg pointer .int) offset) flags).operands = .ok operands)
    {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat} {mp : ArmFault.MemMap}
    (access : AccessAt sb (.load .uload64 (.vreg d .int) (.unsignedOffset (.vreg pointer .int) offset) flags)
      (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world code address bytes)
    (unmapped : ∃ k < bytes,mp (address + BitVec.ofNat 64 k) = .none) : TrapAtF mp R.fb R.base code s := by
  obtain ⟨size,flag,actualAddress⟩ := access.load_inv
  rw [size] at unmapped
  obtain ⟨j,destination,base,destinationBound,baseBound,line,pc,clean,program,uses⟩ :=
    load_unsigned_line (sb := sb) wellFormed related found located
  rw [uses operands valid] at actualAddress
  have range : offset % LoadOp.uload64.bytes = 0 ∧ offset ≤ 4095*LoadOp.uload64.bytes := by
    rcases sourceOffset with rfl | rfl <;> decide
  have addressEq : Arm.read_gpr 64 (BitVec.ofNat 5 base) s + BitVec.ofNat 64 offset = address := by
    simp only [amodeAddr] at actualAddress
    rw [if_pos range] at actualAddress
    have actual := Option.some.inj actualAddress
    rw [lo64_regVal_x] at actual
    simpa [Arm.read_gpr,rnum] using actual
  have marked : R.L[j]? = some (.ins (.load .uload64 (.x destination) (.unsignedOffset (.x base) offset)) (some code)) := by
    simpa only [flag] using line
  have trap := access_trapAt_ins wellFormed marked pc clean
  obtain ⟨inst,encoded,decoded⟩ := access_decodeAt_line wellFormed marked program pc
  have fault := encoded_load64_access_fault (mp := mp) (s := s) (by omega : base ≤ 30) (by omega : destination ≤ 30)
    sourceOffset encoded (by simpa only [addressEq,LoadOp.bytes] using unmapped)
  exact ⟨trap,(ArmFault.faults_iff (show Arm.read_err s = .None from clean) decoded).mpr fault⟩

/-- The checked computed store reaches the original trap-table code before its actual write. -/
theorem store_eight_fault_site {R : RL} (wellFormed : R.Wf) {s : Arm.ArmState}
    {b k stored pointer sb : Nat} {allocs : Array Loc} {items : List RItem}
    {values : Loc → CV} {world : Arm.ArmState} {block : VBlock} {flags : Clif.MemFlags}
    (related : Q R s (.run ⟨b,.op k allocs :: items,values,world⟩))
    (found : R.vc.blocks[b]? = some block)
    (located : block.insts[k]? = some (.store .store64 (.vreg stored .int)
      (.unsignedOffset (.vreg pointer .int) 8) flags)) {operands : Array Operand}
    (valid : (MInst.store .store64 (.vreg stored .int) (.unsignedOffset (.vreg pointer .int) 8) flags).operands = .ok operands)
    {code : Clif.TrapCode} {address : BitVec 64} {bytes : Nat} {mp : ArmFault.MemMap}
    (access : AccessAt sb (.store .store64 (.vreg stored .int) (.unsignedOffset (.vreg pointer .int) 8) flags)
      (((operands.zip allocs).toList.filter (·.1.isUse)).map (values ·.2)) world code address bytes)
    (unmapped : ∃ k < bytes,mp (address + BitVec.ofNat 64 k) = .none) : TrapAtF mp R.fb R.base code s := by
  obtain ⟨value,addressUses,sourceUses,size,flag,actualAddress⟩ := access.store_inv
  rw [size] at unmapped
  obtain ⟨j,valueReg,base,valueBound,baseBound,line,pc,clean,program,uses⟩ :=
    store_unsigned_line (sb := sb) wellFormed related found located
  have tail : addressUses = [regVal s (.x base)] :=
    (List.cons.inj (sourceUses.symm.trans (uses operands valid))).2
  rw [tail] at actualAddress
  have addressEq : Arm.read_gpr 64 (BitVec.ofNat 5 base) s + 8#64 = address := by
    simp only [amodeAddr,StoreOp.bytes,show 8 % 8 = 0 ∧ 8 ≤ 4095*8 from by decide,ite_true] at actualAddress
    have actual := Option.some.inj actualAddress
    rw [lo64_regVal_x] at actual
    simpa [Arm.read_gpr,rnum] using actual
  have marked : R.L[j]? = some (.ins (.store .store64 (.x valueReg) (.unsignedOffset (.x base) 8)) (some code)) := by
    simpa only [flag] using line
  have trap := access_trapAt_ins wellFormed marked pc clean
  obtain ⟨inst,encoded,decoded⟩ := access_decodeAt_line wellFormed marked program pc
  have fault := encoded_store64_eight_access_fault (mp := mp) (s := s) (by omega : base ≤ 30) (by omega : valueReg ≤ 30)
    encoded (by simpa only [addressEq,StoreOp.bytes] using unmapped)
  exact ⟨trap,(ArmFault.faults_iff (show Arm.read_err s = .None from clean) decoded).mpr fault⟩

end Backend.Stock.Proof.MemoryFaults
