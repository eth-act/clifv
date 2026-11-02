import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.SpillClsInst
namespace Backend.Stock.Proof.ScalarDiv
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private theorem alias_renaming (a : Array (Option Nat)) :
    VRenaming (Backend.lowerFunction.resolve a (a.size+1)) (aliasNum a) := by
  refine ⟨fun n c => resolve_vreg a _ n c,?_⟩
  intro r hr
  cases r with
  | vreg n c => exact False.elim (hr n c rfl)
  | _ => simp [Backend.lowerFunction.resolve]
/-- Internal semantics used to prove actual alias-resolved code. -/
def aliasSem (aliases : Array (Option Nat)) (isem : Backend.Proof.Sem) : Backend.Proof.Sem :=
  fun i => isem (i.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))
/-- Refinement is inherited internally by the renamed semantics; callers need
no semantic invariance assumption. -/
theorem stock_div_alias_sem_refines {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (aliases : Array (Option Nat)) : Refines F (aliasSem aliases isem) := by
  intro i us world outs next ctl spec
  have same := ispec_mapRegs (alias_renaming aliases) us world i
  exact refines _ _ _ _ _ (same.trans spec)
private theorem resolve_idempotent (aliases : Array (Option Nat))
    (idem : ∀ n,aliasNum aliases (aliasNum aliases n) = aliasNum aliases n) (r : Reg) :
    Backend.lowerFunction.resolve aliases (aliases.size+1)
      (Backend.lowerFunction.resolve aliases (aliases.size+1) r) =
      Backend.lowerFunction.resolve aliases (aliases.size+1) r := by
  cases r with
  | vreg n c =>
    simp only [resolve_vreg]
    change Reg.vreg (aliasNum aliases (aliasNum aliases n)) c = .vreg (aliasNum aliases n) c
    rw [idem]
  | _ => rfl
private theorem inst_idempotent (aliases : Array (Option Nat))
    (idem : ∀ n,aliasNum aliases (aliasNum aliases n) = aliasNum aliases n) (i : MInst) :
    (i.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      i.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)) := by
  rw [Backend.Proof.Spill.mapRegs_comp]
  have equal : (Backend.lowerFunction.resolve aliases (aliases.size+1) ∘
      Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      Backend.lowerFunction.resolve aliases (aliases.size+1) := funext (resolve_idempotent aliases idem)
  rw [equal]
/-- Alias idempotence derives the invariance needed by the existing renaming
proof, without adding it to the original source input conditions. -/
theorem stock_div_alias_sem_invariant (aliases : Array (Option Nat))
    (idem : ∀ n,aliasNum aliases (aliasNum aliases n) = aliasNum aliases n) (isem : Backend.Proof.Sem) :
    ∀ i,aliasSem aliases isem (i.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
      aliasSem aliases isem i := by
  intro i
  unfold aliasSem
  rw [inst_idempotent aliases idem]
private theorem seqRun_eq_on {sem sem' : Backend.Proof.Sem} :
    ∀ ms : List MInst,(∀ i ∈ ms,sem i = sem' i) → ∀ ρ world,seqRun sem ms ρ world = seqRun sem' ms ρ world := by
  intro ms
  induction ms with
  | nil => intro _ _ _; rfl
  | cons i ms ih =>
    intro same ρ world
    have head := same i (List.mem_cons_self)
    have tail := ih (fun j hj => same j (List.mem_cons_of_mem i hj))
    simp only [seqRun,head,tail]
/-- The internal renamed semantics executes the final renamed code exactly as
the requested machine semantics once actual alias idempotence is available. -/
theorem stock_div_alias_sem_run (aliases : Array (Option Nat))
    (idem : ∀ n,aliasNum aliases (aliasNum aliases n) = aliasNum aliases n)
    (isem : Backend.Proof.Sem) (ms : List MInst) (ρ : Nat → CV) (world : Arm.ArmState) :
    seqRun (aliasSem aliases isem)
      (ms.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world =
    seqRun isem (ms.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world := by
  apply seqRun_eq_on
  intro i member
  obtain ⟨raw,_,rfl⟩ := List.mem_map.mp member
  unfold aliasSem
  rw [inst_idempotent aliases idem]
end Backend.Stock.Proof.ScalarDiv
