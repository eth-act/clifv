import FV.Backend.Proof.StockScanSemantics
import FV.Backend.Proof.IselCmpDiv

/-! Generic prefix/trap composition for the next mixed-body delivery.
No purity, unchanged-world or externally supplied record assumptions enter a
source domain: local obligations are internal proof-composition interfaces. -/
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver
set_option autoImplicit false
set_option Elab.async false

/-- A finite original source prefix reaches an instruction's genuine trap. -/
inductive SourceTrapSteps {S : Type} (step : Nat → S → S → Prop)
    (trap : Nat → S → Clif.TrapCode → Prop) : List Nat → S → Clif.TrapCode → Prop where
  | here {i : Nat} {rest : List Nat} {s : S} {code : Clif.TrapCode}
      (failed : trap i s code) : SourceTrapSteps step trap (i :: rest) s code
  | next {i : Nat} {rest : List Nat} {s t : S} {code : Clif.TrapCode}
      (head : step i s t) (tail : SourceTrapSteps step trap rest t code) :
      SourceTrapSteps step trap (i :: rest) s code

private theorem sourceTrapSteps_append {S : Type} {step : Nat → S → S → Prop}
    {trap : Nat → S → Clif.TrapCode → Prop} {xs ys : List Nat} {s : S} {code : Clif.TrapCode} :
    SourceTrapSteps step trap (xs ++ ys) s code ↔
      SourceTrapSteps step trap xs s code ∨
        ∃ t, SourceSteps step xs s t ∧ SourceTrapSteps step trap ys t code := by
  induction xs generalizing s with
  | nil =>
    constructor
    · intro h; exact Or.inr ⟨s,.nil s,h⟩
    · rintro (impossible | ⟨t,steps,failed⟩)
      · cases impossible
      · cases steps; exact failed
  | cons i xs ih =>
    constructor
    · intro h
      cases h with
      | here failed => exact Or.inl (.here failed)
      | next head tail =>
        rcases ih.mp tail with failed | ⟨t,front,back⟩
        · exact Or.inl (.next head failed)
        · exact Or.inr ⟨t,.cons head front,back⟩
    · rintro (failed | ⟨t,steps,back⟩)
      · cases failed with
        | here failed => exact .here failed
        | next head tail => exact .next head (ih.mpr (Or.inl tail))
      · cases steps with
        | cons head tail => exact .next head (ih.mpr (Or.inr ⟨t,tail,back⟩))

/-- A fall-through prefix can change the world before a real trap. -/
theorem trapRun_seq_prefix {isem : Backend.Proof.Sem} {first rest : List MInst}
    {ρ ρ' : Nat → CV} {w w' : Arm.ArmState} {code : Clif.TrapCode}
    (executed : seqRun isem first ρ w = some (.fall ρ' w'))
    (failed : TrapRun isem rest ρ' w' code) : TrapRun isem (first ++ rest) ρ w code := by
  obtain ⟨offset,i,ops,regs,before,outs,after,run,coded⟩ := failed
  exact ⟨_,i,ops,regs,before,outs,after,seqRun_append_fall_stop isem executed run,coded⟩

/-- The actual selected chunk refines a trapping source instruction. -/
def ScanTrapRefines {S : Type} (sourceTrap : Nat → S → Clif.TrapCode → Prop)
    (sem : Backend.Proof.Sem) (aliases : Array (Option Nat))
    (rel : State → S → (Nat → CV) → Arm.ArmState → Prop) (record : ScanRecord) : Prop :=
  ∀ s code, sourceTrap record.inst s code → ∀ ρ w,
    rel record.output.state s ρ w →
      TrapRun sem (record.output.emitted.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ w code

/-- Real backward scan chunks compose in forward order through the first
source trap. Later chunks do not execute. Source and world relations may carry
memory effects; no pure-run or no-trap shortcut is used. -/
theorem ScansSpec.trap_refines {S : Type} {exec : Nat → State → Except String Scan}
    {source : Nat → S → S → Prop} {sourceTrap : Nat → S → Clif.TrapCode → Prop}
    {sem : Backend.Proof.Sem} {aliases : Array (Option Nat)}
    {rel : State → S → (Nat → CV) → Arm.ArmState → Prop}
    {indices : List Nat} {input : State} {output : BlockScan}
    (scanned : ScansSpec exec indices input output)
    (normal : ∀ r ∈ output.records, ScanFallRefines source sem aliases rel r)
    (trapping : ∀ r ∈ output.records, ScanTrapRefines sourceTrap sem aliases rel r) :
    ∀ s code, SourceTrapSteps source sourceTrap indices.reverse s code → ∀ ρ w,
      rel output.state s ρ w →
      TrapRun sem (output.code.toList.map (·.mapRegs
        (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ w code := by
  induction scanned with
  | nil input =>
    intro s code failed
    cases failed
  | @cons i indices input scan tail head rest ih =>
    intro s code failed ρ w held
    have split : SourceTrapSteps source sourceTrap (indices.reverse ++ [i]) s code := by
      simpa only [List.reverse_cons] using failed
    rcases sourceTrapSteps_append.mp split with front | ⟨mid,front,last⟩
    · have failed := ih (fun r h => normal r (List.mem_cons_of_mem _ h))
        (fun r h => trapping r (List.mem_cons_of_mem _ h)) s code front ρ w held
      simpa only [Array.toList_append,List.map_append] using failed.append
    · obtain ⟨ρ',w',executed,post⟩ := rest.fall_refines
        (fun r h => normal r (List.mem_cons_of_mem _ h)) s mid front ρ w held
      have terminal : sourceTrap i mid code := by
        cases last with
        | here failed => exact failed
        | next stepped impossible => cases impossible
      have failed := trapping ⟨i,input,scan⟩ (List.mem_cons_self ..) mid code terminal ρ' w' post
      simpa only [Array.toList_append,List.map_append] using trapRun_seq_prefix executed failed

end Backend.Stock.Proof
#print axioms Backend.Stock.Proof.trapRun_seq_prefix
#print axioms Backend.Stock.Proof.ScansSpec.trap_refines
