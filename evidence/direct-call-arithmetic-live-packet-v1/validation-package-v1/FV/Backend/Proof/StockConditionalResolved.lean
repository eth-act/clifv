import FV.Backend.Proof.StockConditionalValues

namespace Backend.Stock.Proof.ConditionalValues
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

/-- The flag branch replacement follows the actual final resolver. Its proof
companion's fresh result remains an identity; no source register identity is
assumed and the companion is absent from the real branch code. -/
theorem flag_branch_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {leading : List MInst} {aliases : Array (Option Nat)}
    {ρ : Nat → CV} {world : Arm.ArmState} {d : Nat} {condition : Cond}
    (valid : condition ≠ .al ∧ condition ≠ .nv) {b : Bool} {P : Nat → Prop}
    (bounded : aliases.size ≤ d) (outside : ∀ k,P k → k ≠ d)
    (run : Runs F isem ((leading++[MInst.cset (.vreg d .int) condition]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ ∀ k,P k → final k = ρ k))
    (yes no : Label) :
    ∃ regs prefixWorld branchWorld,
      seqRun isem ((leading++[MInst.condBr yes no (.cond condition)]).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world =
        some (.stop leading.length (.condBr yes no (.cond condition)) #[] regs prefixWorld
          [] branchWorld (.goto (if b then 0 else 1))) ∧
      SameWorldNF F branchWorld world ∧ ∀ k,P k → regs k = ρ k := by
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have mapBoolean : (MInst.cset (.vreg d .int) condition).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = .cset (.vreg d .int) condition := by
    simp only [MInst.mapRegs,resolve_vreg]
    change MInst.cset (.vreg (aliasNum aliases d) .int) condition = _
    rw [fresh]
  have mapBranch : (MInst.condBr yes no (.cond condition)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = .condBr yes no (.cond condition) := rfl
  simp only [List.map_append,List.map_cons,List.map_nil,mapBoolean] at run
  simp only [List.map_append,List.map_cons,List.map_nil,mapBranch]
  simpa only [List.length_map] using branch_of_boolean_companion refines valid outside run yes no

/-- Direct zero/nonzero branching reads the final resolved original operand,
removing the ghost comparison and boolean result. -/
theorem zero_branch_resolved {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) {leading : List MInst} {aliases : Array (Option Nat)}
    {ρ : Nat → CV} {world : Arm.ArmState} {d : Nat} {b : Bool} {P : Nat → Prop}
    (nonzero : Bool) (size : OperandSize) (key : Nat) (bounded : aliases.size ≤ d)
    (outside : ∀ k,P k → k ≠ d)
    (run : Runs F isem ((leading++[cmpImm0 size key,
      MInst.cset (.vreg d .int) (if nonzero then Cond.ne else Cond.eq)]).map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 b⟩ (final d) ∧ ∀ k,P k → final k = ρ k))
    (yes no : Label) :
    ∃ regs prefixWorld branchWorld,
      seqRun isem ((leading++[MInst.condBr yes no
        (if nonzero then .notZero (.vreg key .int) size else .zero (.vreg key .int) size)]).map
        (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world =
        some (.stop leading.length (.condBr yes no
          (if nonzero then .notZero (.vreg (aliasNum aliases key) .int) size
            else .zero (.vreg (aliasNum aliases key) .int) size))
          #[⟨aliasNum aliases key,.int,.use,.early,.reg⟩] regs prefixWorld [] branchWorld
          (.goto (if b then 0 else 1))) ∧
      SameWorldNF F branchWorld world ∧ ∀ k,P k → regs k = ρ k := by
  have fresh : aliasNum aliases d = d := by
    apply chaseF_none
    rw [Array.getElem?_eq_none bounded]
    rfl
  have mapBoolean : (MInst.cset (.vreg d .int) (if nonzero then Cond.ne else Cond.eq)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = .cset (.vreg d .int) (if nonzero then Cond.ne else Cond.eq) := by
    simp only [MInst.mapRegs,resolve_vreg]
    change MInst.cset (.vreg (aliasNum aliases d) .int) (if nonzero then Cond.ne else Cond.eq) = _
    rw [fresh]
  have mapImmediate : (cmpImm0 size key).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) = cmpImm0 size (aliasNum aliases key) := by
    simp only [cmpImm0,MInst.mapRegs,resolve_vreg]
    rfl
  have mapBranch : (MInst.condBr yes no (if nonzero then .notZero (.vreg key .int) size else .zero (.vreg key .int) size)).mapRegs
      (Backend.lowerFunction.resolve aliases (aliases.size+1)) =
      .condBr yes no (if nonzero then .notZero (.vreg (aliasNum aliases key) .int) size
        else .zero (.vreg (aliasNum aliases key) .int) size) := by
    cases nonzero <;> simp only [Bool.false_eq_true,ite_false,ite_true,MInst.mapRegs,CondBrKind.mapRegs,resolve_vreg] <;> rfl
  simp only [List.map_append,List.map_cons,List.map_nil,mapImmediate,mapBoolean] at run
  simp only [List.map_append,List.map_cons,List.map_nil,mapBranch]
  simpa only [List.length_map] using zero_branch_of_boolean_companion refines nonzero size
    (aliasNum aliases key) outside run yes no

end Backend.Stock.Proof.ConditionalValues
