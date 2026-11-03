import FV.Backend.Proof.StockAcquirePrepareNoHooks
import FV.Backend.Proof.StockEntryAssembly
import FV.Backend.Proof.StockAcquireReturnCoreCode

namespace Backend.Stock.Proof.Acquire810
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false
attribute [local irreducible] Stock.runTerm emitBranch collectOutgoing scanBlock

/-- Register renaming preserves the instruction's model hooks classification. -/
theorem noHookInst_mapRegs {inst : MInst} (noHook : NoHookInst inst) (rename : Reg → Reg) :
    NoHookInst (inst.mapRegs rename) := by
  cases inst <;> simp_all [NoHookInst,MInst.mapRegs]

/-- Both register copies and stack loads in the actual ABI prelude are instructions without model hooks. -/
theorem entry_prelude_no_hook (rows : List MappedEntryRow) :
    ∀ inst ∈ (entryPrelude (mappedEntryPairs rows) (mappedEntryLoads rows)).toList,NoHookInst inst := by
  have loads : ∀ inst ∈ (mappedEntryLoads rows).toList,NoHookInst inst := by
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

/-- Actual entry assembly preserves a body without model hooks without a restriction on stack arguments. -/
theorem assembled_entry_no_hook {ctx : Ctx} {f : Clif.Function} {source : Clif.Block}
    {label : Nat} {targets : Array Nat} {outgoing : Array (Array Reg)}
    {bytes : List Nat} {uses : Array UseState} {body : Array MInst} {block : VBlock}
    (run : assembleOriginalBlock ctx f source 0 label targets outgoing bytes uses body = .ok block)
    (noHook : ∀ inst ∈ body.toList,NoHookInst inst) :
    ∀ inst ∈ block.insts.toList,NoHookInst inst := by
  obtain ⟨locs,stack,rows,signature,mapped,ordered,lookups,rfl⟩ := assemble_entry_source_rows run
  intro inst member
  simp only [Array.toList_append,List.mem_append] at member
  rcases member with member | member
  · exact entry_prelude_no_hook rows inst member
  · exact noHook inst member

end Backend.Stock.Proof.Acquire810
