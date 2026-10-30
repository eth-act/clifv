import FV.Backend.Proof.StockValues
import FV.Backend.Proof.LowerSim
namespace Backend.Stock.Proof
open Backend.Proof Backend.Proof.Driver Isle Isle.Aarch64
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192

/-- Existing ABI stack-load semantics preserve all seeded source values;
parameters omitted from the load list retain their initial virtual values. -/
theorem entry_loads_preserve_values {ctx : Ctx} {fr : Clif.Frame}
    {isem : Backend.Proof.Sem} {F : BitVec 64 → Prop} {sb : Nat} {syms : String → Option Nat}
    (memorySem : MemRefines F sb syms isem) {MR : MemRelT} (stable : MRStable F MR)
    (entries : List (((Nat × Clif.Ty) × ArgLoc) × Nat))
    (nodup : (entries.map (·.1.1.1)).Nodup)
    {ρ : Nat → CV} {w : Arm.ArmState} {cm : Clif.Mem}
    (held : ValuesHeld (fun _ => True) ctx fr ρ) (memory : MR fr.slots cm w)
    (safe : ∀ q ∈ entries, ∀ off, q.1.2 = .stack off →
      (q.2 = 1 ∨ q.2 = 2 ∨ q.2 = 4 ∨ q.2 = 8) ∧
      Avoids F q.2 (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))))
    (physical : ∀ x v key q off, fr.regs x = some v →
      ctx.valueReg? x = some (.vreg key .int) → q ∈ entries → q.1.1.1 = key →
      q.1.2 = .stack off → VHolds v (ofX (loadVal (loadOpOfBytes q.2)
        (Arm.r (.GPR 29#5) w + BitVec.ofInt 64 (16 + (off : Int))) w))) :
    ∃ ρ' w', seqRun isem (entries.filterMap (entryLoadOf id)) ρ w = some (.fall ρ' w') ∧
      MR fr.slots cm w' ∧ ValuesHeld (fun _ => True) ctx fr ρ' ∧ SameWorld F w' w := by
  obtain ⟨ρ',w',execution,mem,other,reg,stack,same⟩ :=
    entryLoads_run (R := id) memorySem stable entries ρ fr.slots cm w
      (by intro q member; rfl) nodup safe memory
  refine ⟨ρ',w',execution,mem,?_,same⟩
  intro x _ v found
  obtain ⟨key,mapped,value⟩ := held x trivial v found
  refine ⟨key,mapped,?_⟩
  by_cases inside : key ∈ entries.map (·.1.1.1)
  · obtain ⟨q,member,equal⟩ := List.mem_map.mp inside
    cases location : q.1.2 with
    | reg pin =>
      have kept := reg q member pin location
      rw [← equal,kept]
      simpa only [equal] using value
    | stack off =>
      have read := stack q member off location
      rw [← equal,read]
      exact physical x v key q off found mapped member equal location
  · rw [other key inside]
    exact value
end Backend.Stock.Proof
