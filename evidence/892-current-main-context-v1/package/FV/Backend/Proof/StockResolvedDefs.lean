import FV.Backend.Proof.IselCmpRun
import FV.Backend.Proof.StockAliasSemantics
import FV.Backend.Proof.LowerRename

namespace Backend.Stock.Proof.Resolved
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

theorem renamed_defs (aliases : Array (Option Nat)) (m : MInst) :
    vdefs (m.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))) =
      (vdefs m).map (aliasNum aliases) := by
  have aliasRenaming : VRenaming (Backend.lowerFunction.resolve aliases (aliases.size+1)) (aliasNum aliases) := by
    refine ⟨fun n c => resolve_vreg aliases _ n c,?_⟩
    intro r notVirtual
    cases r with
    | vreg n c => exact False.elim (notVirtual n c rfl)
    | _ => simp [Backend.lowerFunction.resolve]
  unfold vdefs
  rw [operands_mapRegs aliasRenaming]
  cases m.operands with
  | error e => rfl
  | ok ops =>
    simp only [Except.map,Array.toList_map]
    rw [filter_map_rn _ Operand.isDef (fun _ => rfl)]
    simp only [List.map_map]
    rfl

/-- Actual fresh-definition intervals survive final alias resolution because
all definitions are outside the alias table and therefore remain identities. -/
theorem fragment_defs {before next : LState} {code : List MInst}
    (fragment : Frag before next code) (aliases : Array (Option Nat))
    (bounded : aliases.size ≤ before.nextVreg) :
    ∀ inst ∈ code.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))),
      ∀ key ∈ vdefs inst,before.nextVreg ≤ key ∧ key < next.nextVreg := by
  intro inst member key defined
  obtain ⟨original,inside,rfl⟩ := List.mem_map.mp member
  rw [renamed_defs] at defined
  obtain ⟨originalKey,originalDef,rfl⟩ := List.mem_map.mp defined
  have interval := fragment.defs original inside originalKey originalDef
  have identity : aliasNum aliases originalKey = originalKey := by
    apply chaseF_none
    rw [Array.getElem?_eq_none (by omega)]
    rfl
  rw [identity]
  exact interval

/-- The real producer prefix preserves every register outside its own fresh
interval, including an unexecuted proof companion's number at the endpoint. -/
theorem fragment_frame {V W : Type} {sem : ISem V W} {before next : LState} {code : List MInst}
    (fragment : Frag before next code) (aliases : Array (Option Nat))
    (bounded : aliases.size ≤ before.nextVreg) {ρ final : Nat → V} {world endWorld : W}
    (run : seqRun sem (code.map (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1))))
      ρ world = some (.fall final endWorld)) :
    ∀ key,key < before.nextVreg ∨ next.nextVreg ≤ key → final key = ρ key := by
  intro key outside
  apply seqRun_frame sem run key
  intro inst member defined
  have interval := fragment_defs fragment aliases bounded inst member key defined
  rcases outside with lower | upper <;> omega

/-- A nonidentity alias changes a real defined register exactly as predicted. -/
theorem renamed_defs_witness :
    vdefs ((MInst.extend (.vreg 1 .int) (.vreg 0 .int) false 8 32).mapRegs
      (Backend.lowerFunction.resolve #[none,some 3] 3)) = [3] ∧
    vdefs (MInst.extend (.vreg 1 .int) (.vreg 0 .int) false 8 32) = [1] := by
  constructor
  · have derived := renamed_defs #[none,some 3] (MInst.extend (.vreg 1 .int) (.vreg 0 .int) false 8 32)
    change _ = [3] at derived
    exact derived
  · rfl

end Backend.Stock.Proof.Resolved
