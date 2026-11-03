import FV.Backend.Proof.StockAcquirePrepareNoCall
import FV.Backend.Proof.StockEntryAssembly
import FV.Backend.Proof.StockAcquireReturnCoreCode

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Stock.runTerm emitBranch collectOutgoing scanBlock

/-- Register renaming preserves the instruction's call classification. -/
theorem noCallInst_mapRegs {inst : MInst} (noCall : NoCallInst inst) (rename : Reg → Reg) :
    NoCallInst (inst.mapRegs rename) := by
  cases inst <;> simp_all [NoCallInst,MInst.mapRegs]

/-- Both register copies and stack loads in the actual ABI prelude are non-calls. -/
theorem entry_prelude_no_call (rows : List MappedEntryRow) :
    ∀ inst ∈ (entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows)).toList,NoCallInst inst := by
  have loads : ∀ inst ∈ (mappedEntryLoads rows).toList,NoCallInst inst := by
    intro inst member
    simp only [mappedEntryLoads,List.toList_toArray,List.mem_filterMap] at member
    obtain ⟨row,member,located⟩ := member
    cases loc : row.input.1.2 with
    | reg pin => simp only [loc] at located;cases located
    | stack off => simp only [loc] at located;cases located;trivial
  intro inst member
  unfold entryPrelude at member
  split at member
  · simp only [Array.toList_append,List.mem_append,List.mem_singleton] at member
    rcases member with rfl | member
    · trivial
    · exact loads inst member
  · exact loads inst member

/-- Actual entry assembly preserves a non-call body without a restriction on stack arguments. -/
theorem assembled_entry_no_call {ctx : Ctx} {f : Clif.Function} {source : Clif.Block}
    {label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {bytes : List Nat} {uses : Array UseState} {body : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f source 0 label targets outgoing bytes uses body = .ok block)
    (noCall : ∀ inst ∈ body.toList,NoCallInst inst) :
    ∀ inst ∈ block.insts.toList,NoCallInst inst := by
  obtain ⟨locs,stack,rows,signature,mapped,ordered,lookups,rfl⟩ := assemble_entry_source_rows run
  intro inst member
  simp only [Array.toList_append,List.mem_append] at member
  rcases member with member | member
  · exact entry_prelude_no_call rows inst member
  · exact noCall inst member

end Backend.Stock.Proof.Acquire810
