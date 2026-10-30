import FV.Backend.Proof.StockCmpMachineValues
import FV.Backend.Proof.StockSelectReplacementResolved
namespace Backend.Stock.Proof.ScalarSelect.ReplacementWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
private def registers (k : Nat) : CV := BitVec.ofNat 128 (2^100 + if k = 1 then 7 else 9)
private def condition (chooseX : Bool) : Cond := if chooseX then .eq else .ne
private theorem comparison_run (ty : Clif.Ty)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (chooseX : Bool) (world : Arm.ArmState) :
    Runs (fun _ => True) ispec
      ([MInst.aluRRR .subS .size64 .xzr (.vreg 1 .int) (.vreg 1 .int)]++[.cset (.vreg 4 .int) (condition chooseX)])
      registers world (fun final _ => VHolds ⟨.i8,Clif.Sem.bool8 chooseX⟩ (final 4) ∧
        VHolds ⟨ty,BitVec.ofNat ty.width 7⟩ (final 1) ∧ VHolds ⟨ty,BitVec.ofNat ty.width 9⟩ (final 3) ∧
        ∀ k,k ≠ 4 → final k = registers k) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have flags := setsFlags_cmpRR .size64 1 1 registers
  have truth : condOn (condition chooseX).bits
      (cmpFlags (opnd .size64 (registers 1)) (opnd .size64 (registers 1))) = chooseX := by
    cases chooseX <;> decide +kernel
  have valid : condition chooseX ≠ .al ∧ condition chooseX ≠ .nv := by cases chooseX <;> decide +kernel
  have originalX : VHolds ⟨ty,BitVec.ofNat ty.width 7⟩ (registers 1) := by
    change (registers 1).setWidth ty.width = BitVec.ofNat ty.width 7
    rcases width with w | w | w | w <;> rw [w] <;> decide +kernel
  have originalY : VHolds ⟨ty,BitVec.ofNat ty.width 9⟩ (registers 3) := by
    change (registers 3).setWidth ty.width = BitVec.ofNat ty.width 9
    rcases width with w | w | w | w <;> rw [w] <;> decide +kernel
  have boolean := ScalarCmp.stock_cmp_flags_cset self flags truth valid 4 world
  have established : Runs (fun _ => True) ispec
      ([MInst.aluRRR .subS .size64 .xzr (.vreg 1 .int) (.vreg 1 .int)]++[.cset (.vreg 4 .int) (condition chooseX)])
      registers world (fun final _ => VHolds ⟨.i8,Clif.Sem.bool8 chooseX⟩ (final 4) ∧
        VHolds ⟨ty,BitVec.ofNat ty.width 7⟩ (final 1) ∧ VHolds ⟨ty,BitVec.ofNat ty.width 9⟩ (final 3) ∧
        ∀ k,k ≠ 4 → final k = registers k) := by
    apply boolean.imp
    intro final _ _ equal
    subst final
    refine ⟨?_,?_,?_,?_⟩
    · rw [upd_same]
      cases chooseX <;> unfold VHolds <;> decide +kernel
    · simpa only [upd,show (1:Nat) ≠ 4 by decide,ite_false] using originalX
    · simpa only [upd,show (3:Nat) ≠ 4 by decide,ite_false] using originalY
    · intro k hk
      simp only [upd,hk,ite_false]
  exact established
/-- Both outcomes and all four scalar widths inhabit replacement of an actual
compare/cset run by compare/csel. Inputs have distinct values and dirty upper
bits; every register except the fresh destination remains unchanged. -/
theorem stock_select_replacement_witness (ty : Clif.Ty)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (chooseX : Bool) (world : Arm.ArmState) :
    Runs (fun _ => True) ispec
      [.aluRRR .subS .size64 .xzr (.vreg 1 .int) (.vreg 1 .int),
        .csel (.vreg 4 .int) (.vreg 1 .int) (.vreg 3 .int) (condition chooseX)] registers world
      (fun final _ => VHolds ⟨ty,if chooseX then BitVec.ofNat ty.width 7 else BitVec.ofNat ty.width 9⟩ (final 4) ∧
        ∀ k,k ≠ 4 → final k = registers k) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have valid : condition chooseX ≠ .al ∧ condition chooseX ≠ .nv := by cases chooseX <;> decide +kernel
  have established := comparison_run ty width chooseX world
  obtain ⟨final,endWorld,actual,_,_⟩ := established
  exact stock_select_replace_cset_from_spec self (by omega) (by decide) (by decide) (fun _ h => h)
    ⟨final,endWorld,actual⟩ (comparison_run ty width chooseX world)
private def aliases : Array (Option Nat) := #[some 1,none,some 3,none]
/-- Nonidentity source aliases and a fresh destination inhabit the actual final
resolver variant at every scalar width and both selected outcomes. -/
theorem stock_select_replacement_alias_witness (ty : Clif.Ty)
    (width : ty.width = 8 ∨ ty.width = 16 ∨ ty.width = 32 ∨ ty.width = 64)
    (chooseX : Bool) (world : Arm.ArmState) :
    Runs (fun _ => True) ispec
      ([MInst.aluRRR .subS .size64 .xzr (.vreg 0 .int) (.vreg 0 .int),
        .csel (.vreg 4 .int) (.vreg 0 .int) (.vreg 2 .int) (condition chooseX)].map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) registers world
      (fun final _ => VHolds ⟨ty,if chooseX then BitVec.ofNat ty.width 7 else BitVec.ofNat ty.width 9⟩ (final 4) ∧
        ∀ k,k ≠ 4 → final k = registers k) := by
  have self : Refines (fun _ => True) ispec := fun _ _ _ _ w' _ h => ⟨w',h,SameWorld.refl _ _⟩
  have valid : condition chooseX ≠ .al ∧ condition chooseX ≠ .nv := by cases chooseX <;> decide +kernel
  apply stock_select_replace_cset_resolved (leading := [MInst.aluRRR .subS .size64 .xzr (.vreg 0 .int) (.vreg 0 .int)])
    (aliases := aliases) (d := 4) (x := 0) (y := 2) self valid (by omega) (by decide) (by decide +kernel)
    (by decide +kernel) (fun _ h => h)
  exact comparison_run ty width chooseX world
end Backend.Stock.Proof.ScalarSelect.ReplacementWitness
