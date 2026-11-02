import FV.Backend.Proof.StockMemoryAccessScanTrap
import FV.Backend.Proof.StockDivReturnRefines

/-! Draft: staged source only; no kernel command ran. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A local access boundary reaches the actual placed VCode instruction. -/
theorem accessTrapRun_at {sb : Nat} {vc : VCode} {isem : Backend.Proof.Sem}
    {label start : Nat} {block : VBlock} {code : List MInst}
    (placed : vc.blocks[label]? = some block) (segment : SegAt block start code)
    {ρ : Nat → CV} {world : Arm.ArmState} {trap : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (reached : AccessTrapRun sb isem code ρ world trap property) :
    VAccessTrapFrom sb vc isem ⟨label,start,ρ,world⟩ trap property := by
  obtain ⟨prefix,inst,suffix,regs,next,operands,uses,address,bytes,
    parts,executed,decoded,inputs,access,allowed⟩ := reached
  rw [parts] at segment
  have before : SegAt block start prefix := segment.append_left
  have instruction : block.insts[start+prefix.length]? = some inst := segment.append_right.head
  have room : start+prefix.length < block.insts.size :=
    (Array.getElem?_eq_some_iff.mp instruction).1
  have path := seqRun_fall_star (vc := vc) (sem := isem) placed before room executed
  exact ⟨label,start+prefix.length,regs,next,block,inst,operands,uses,address,bytes,
    path,placed,instruction,decoded,inputs,access,allowed⟩

/-- Both local trap variants transfer to the actual complete VCode function. -/
theorem trapOrAccessRun_at {sb : Nat} {vc : VCode} {isem : Backend.Proof.Sem}
    {label start : Nat} {block : VBlock} {code : List MInst}
    (placed : vc.blocks[label]? = some block) (segment : SegAt block start code)
    {ρ : Nat → CV} {world : Arm.ArmState} {trap : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (reached : TrapOrAccessRun sb isem code ρ world trap property) :
    VTrapFrom vc isem ⟨label,start,ρ,world⟩ trap ∨
      VAccessTrapFrom sb vc isem ⟨label,start,ρ,world⟩ trap property := by
  rcases reached with explicit | memory
  · exact .inl (DivBody.trapRun_at placed segment explicit)
  · exact .inr (accessTrapRun_at placed segment memory)

/-- A reached actual instruction proves that its initial segment is in bounds. -/
theorem trapOrAccessRun_inbounds {sb : Nat} {isem : Backend.Proof.Sem}
    {block : VBlock} {start : Nat} {code : List MInst} (segment : SegAt block start code)
    {ρ : Nat → CV} {world : Arm.ArmState} {trap : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (reached : TrapOrAccessRun sb isem code ρ world trap property) : start < block.insts.size := by
  cases code with
  | nil =>
    rcases reached with explicit | memory
    · obtain ⟨k,inst,operands,regs,next,outs,final,run,flag⟩ := explicit
      cases run
    · obtain ⟨prefix,inst,suffix,regs,next,operands,uses,address,bytes,parts,rest⟩ := memory
      have length := congrArg List.length parts
      simp only [List.length_nil,List.length_append,List.length_cons] at length
      omega
  | cons inst rest => exact (Array.getElem?_eq_some_iff.mp segment.head).1

end Backend.Stock.Proof.MemoryFaults
