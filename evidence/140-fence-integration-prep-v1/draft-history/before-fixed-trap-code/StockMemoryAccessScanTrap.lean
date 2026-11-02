import FV.Backend.Proof.StockMemoryAccessTrap
import FV.Backend.Proof.StockScanTrapSemantics

/-! Draft: source-only implementation. No kernel command ran. -/
namespace Backend.Stock.Proof.MemoryFaults
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A local emitted chunk reaches its real memory access before that access executes. -/
def AccessTrapRun (sb : Nat) (isem : Backend.Proof.Sem) (code : List MInst)
    (ρ : Nat → CV) (world : Arm.ArmState) (trap : Clif.TrapCode)
    (property : BitVec 64 → Nat → Prop) : Prop :=
  ∃ prefix inst suffix regs next operands uses address bytes,
    code = prefix ++ inst :: suffix ∧ seqRun isem prefix ρ world = some (.fall regs next) ∧
    inst.operands = .ok operands ∧ vuses operands regs = uses ∧
    AccessAt sb inst uses next trap address bytes ∧ property address bytes

theorem AccessTrapRun.append {sb : Nat} {isem : Backend.Proof.Sem} {first rest : List MInst}
    {ρ : Nat → CV} {world : Arm.ArmState} {trap : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (reached : AccessTrapRun sb isem first ρ world trap property) :
    AccessTrapRun sb isem (first ++ rest) ρ world trap property := by
  obtain ⟨prefix,inst,suffix,regs,next,operands,uses,address,bytes,code,executed,tail⟩ := reached
  refine ⟨prefix,inst,suffix ++ rest,regs,next,operands,uses,address,bytes,?_,executed,tail⟩
  rw [code,List.append_assoc]
  rfl

theorem AccessTrapRun.prefix {sb : Nat} {isem : Backend.Proof.Sem} {first rest : List MInst}
    {ρ regs : Nat → CV} {world next : Arm.ArmState} {trap : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (executed : seqRun isem first ρ world = some (.fall regs next))
    (reached : AccessTrapRun sb isem rest regs next trap property) :
    AccessTrapRun sb isem (first ++ rest) ρ world trap property := by
  obtain ⟨prefix,inst,suffix,finalRegs,finalWorld,operands,uses,address,bytes,
    code,prefixRun,tail⟩ := reached
  refine ⟨first ++ prefix,inst,suffix,finalRegs,finalWorld,operands,uses,address,bytes,
    ?_,seqRun_append_fall' isem executed prefixRun,tail⟩
  rw [code,List.append_assoc]

/-- Explicit traps and memory-access boundaries remain separate outcomes. -/
def TrapOrAccessRun (sb : Nat) (isem : Backend.Proof.Sem) (code : List MInst)
    (ρ : Nat → CV) (world : Arm.ArmState) (trap : Clif.TrapCode)
    (property : BitVec 64 → Nat → Prop) : Prop :=
  TrapRun isem code ρ world trap ∨ AccessTrapRun sb isem code ρ world trap property

theorem TrapOrAccessRun.append {sb : Nat} {isem : Backend.Proof.Sem} {first rest : List MInst}
    {ρ : Nat → CV} {world : Arm.ArmState} {trap : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (reached : TrapOrAccessRun sb isem first ρ world trap property) :
    TrapOrAccessRun sb isem (first ++ rest) ρ world trap property := by
  rcases reached with explicit | memory
  · exact .inl explicit.append
  · exact .inr memory.append

theorem TrapOrAccessRun.prefix {sb : Nat} {isem : Backend.Proof.Sem} {first rest : List MInst}
    {ρ regs : Nat → CV} {world next : Arm.ArmState} {trap : Clif.TrapCode}
    {property : BitVec 64 → Nat → Prop}
    (executed : seqRun isem first ρ world = some (.fall regs next))
    (reached : TrapOrAccessRun sb isem rest regs next trap property) :
    TrapOrAccessRun sb isem (first ++ rest) ρ world trap property := by
  rcases reached with explicit | memory
  · exact .inl (trapRun_seq_prefix executed explicit)
  · exact .inr (memory.prefix executed)

/-- Internal local fault obligation; this is not an accepted-source predicate. -/
def LocalAccessTrapRefines {S : Type} (trap : Nat → S → Clif.TrapCode → Prop)
    (sb : Nat) (isem : Backend.Proof.Sem) (aliases : Array (Option Nat))
    (rel : State → S → (Nat → CV) → Arm.ArmState → Prop)
    (property : BitVec 64 → Nat → Prop) (record : ScanRecord) : Prop :=
  ∀ s code,trap record.inst s code → ∀ ρ world,rel record.output.state s ρ world →
    TrapOrAccessRun sb isem (record.output.emitted.toList.map (·.mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world code property

private theorem sourceTrap_append {S : Type} {step : Nat → S → S → Prop}
    {trap : Nat → S → Clif.TrapCode → Prop} {xs ys : List Nat} {s : S} {code : Clif.TrapCode} :
    SourceTrapSteps step trap (xs ++ ys) s code ↔
      SourceTrapSteps step trap xs s code ∨
        ∃ mid,SourceSteps step xs s mid ∧ SourceTrapSteps step trap ys mid code := by
  induction xs generalizing s with
  | nil =>
    constructor
    · intro failed; exact .inr ⟨s,.nil s,failed⟩
    · rintro (impossible | ⟨mid,steps,failed⟩)
      · cases impossible
      · cases steps; exact failed
  | cons i xs ih =>
    constructor
    · intro failed
      cases failed with
      | here head => exact .inl (.here head)
      | next head tail =>
        rcases ih.mp tail with failed | ⟨mid,front,back⟩
        · exact .inl (.next head failed)
        · exact .inr ⟨mid,.cons head front,back⟩
    · rintro (failed | ⟨mid,steps,failed⟩)
      · cases failed with
        | here head => exact .here head
        | next head tail => exact .next head (ih.mpr (.inl tail))
      · cases steps with
        | cons head tail => exact .next head (ih.mpr (.inr ⟨mid,tail,failed⟩))

/-- Real backward records compose the first explicit trap or memory-access boundary.
Earlier normal chunks retain their actual effects on registers and memory. -/
theorem scans_access_trap_refines {S : Type} {exec : Nat → State → Except String Scan}
    {source : Nat → S → S → Prop} {trap : Nat → S → Clif.TrapCode → Prop}
    {sb : Nat} {isem : Backend.Proof.Sem} {aliases : Array (Option Nat)}
    {rel : State → S → (Nat → CV) → Arm.ArmState → Prop}
    {property : BitVec 64 → Nat → Prop} {indices : List Nat} {input : State} {output : BlockScan}
    (scanned : ScansSpec exec indices input output)
    (normal : ∀ record ∈ output.records,ScanFallRefines source isem aliases rel record)
    (trapping : ∀ record ∈ output.records,LocalAccessTrapRefines trap sb isem aliases rel property record) :
    ∀ s code,SourceTrapSteps source trap indices.reverse s code → ∀ ρ world,
      rel output.state s ρ world → TrapOrAccessRun sb isem
        (output.code.toList.map (·.mapRegs
          (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world code property := by
  induction scanned with
  | nil input => intro s code failed; cases failed
  | @cons i indices input scan tail head rest ih =>
    intro s code failed ρ world held
    have split : SourceTrapSteps source trap (indices.reverse ++ [i]) s code := by
      simpa only [List.reverse_cons] using failed
    rcases sourceTrap_append.mp split with front | ⟨mid,front,last⟩
    · have reached := ih (fun record h => normal record (List.mem_cons_of_mem _ h))
        (fun record h => trapping record (List.mem_cons_of_mem _ h)) s code front ρ world held
      simpa only [Array.toList_append,List.map_append] using reached.append
    · obtain ⟨regs,next,executed,post⟩ := rest.fall_refines
        (fun record h => normal record (List.mem_cons_of_mem _ h)) s mid front ρ world held
      have terminal : trap i mid code := by
        cases last with
        | here terminal => exact terminal
        | next stepped impossible => cases impossible
      have reached := trapping ⟨i,input,scan⟩ (List.mem_cons_self ..) mid code terminal regs next post
      simpa only [Array.toList_append,List.map_append] using reached.prefix executed

end Backend.Stock.Proof.MemoryFaults
