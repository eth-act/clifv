import FV.Backend.Proof.StockConditionalResolved

namespace Backend.Stock.Proof.ConditionalValues.ResolvedWitness
open Backend.Proof Backend.Proof.Driver Isle Isle.Interp Isle.Aarch64
set_option autoImplicit false

private def aliases : Array (Option Nat) := #[some 1]
private def truth (nonzero : Bool) (size : OperandSize) (ρ : Nat → CV) : Bool :=
  if nonzero then opnd size (ρ 1) != 0 else opnd size (ρ 1) == 0

private theorem companion {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (ρ : Nat → CV) (world : Arm.ArmState)
    (nonzero : Bool) (size : OperandSize) :
    Runs F isem ([cmpImm0 size 0,MInst.cset (.vreg 1 .int) (if nonzero then .ne else .eq)].map
      (·.mapRegs (Backend.lowerFunction.resolve aliases (aliases.size+1)))) ρ world (fun final _ =>
        VHolds ⟨.i8,Clif.Sem.bool8 (truth nonzero size ρ)⟩ (final 1) ∧ ∀ k,k ≠ 1 → final k = ρ k) := by
  have flags : condOn (if nonzero then Cond.ne else Cond.eq).bits
      (cmpFlags (opnd size (ρ 1)) 0) = truth nonzero size ρ := by
    cases nonzero
    · exact ScalarCmp.stock_cmp_zero_flag _ _
    · exact ScalarCmp.stock_cmp_conditions (n := size.bits) (by cases size <;> simp [OperandSize.bits]) .ne _ _
  have valid : (if nonzero then Cond.ne else Cond.eq) ≠ .al ∧ (if nonzero then Cond.ne else Cond.eq) ≠ .nv := by
    cases nonzero <;> decide
  obtain ⟨final,endWorld,run,nf,updated⟩ := ScalarCmp.stock_cmp_flags_cset refines
    (setsFlags_cmp_imm0 size 1 ρ) flags valid 1 world
  change Runs F isem [cmpImm0 size 1,MInst.cset (.vreg 1 .int) (if nonzero then .ne else .eq)] ρ world _
  refine ⟨final,endWorld,run,nf,?_⟩
  rw [updated]
  constructor
  · rw [upd_same]
    cases truth nonzero size ρ <;> rfl
  · intro k different
    simp only [upd,different,ite_false]

/-- Nonidentity source alias0→1 is used by the real flag producer. The proof
companion destination1 is removed; the real prefix/branch execute for all words. -/
theorem flag_resolved_witness {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (ρ : Nat → CV) (world : Arm.ArmState) :
    ∃ regs prefixWorld branchWorld,
      seqRun isem [cmpImm0 .size64 1,.condBr 2 1 (.cond .eq)] ρ world =
        some (.stop 1 (.condBr 2 1 (.cond .eq)) #[] regs prefixWorld [] branchWorld
          (.goto (if opnd .size64 (ρ 1) == 0 then 0 else 1))) ∧
      SameWorldNF F branchWorld world ∧ ∀ k,k ≠ 1 → regs k = ρ k := by
  exact flag_branch_resolved refines (aliases := aliases) (leading := [cmpImm0 .size64 0])
    (d := 1) (by decide : Cond.eq ≠ .al ∧ Cond.eq ≠ .nv) (by decide)
    (P := fun k => k ≠ 1) (fun _ h => h) (companion refines ρ world false .size64) 2 1

/-- Both widths/polarities use nonidentity source alias0→1. The real direct
branch reads register1 even though the removed companion also used1 as its
boolean destination, exercising this otherwise easy-to-miss boundary. -/
theorem zero_resolved_witness {F : BitVec 64 → Prop} {isem : Backend.Proof.Sem}
    (refines : Refines F isem) (ρ : Nat → CV) (world : Arm.ArmState)
    (nonzero : Bool) (size : OperandSize) :
    ∃ regs prefixWorld branchWorld,
      seqRun isem [.condBr 2 1 (if nonzero then .notZero (.vreg 1 .int) size else .zero (.vreg 1 .int) size)] ρ world =
        some (.stop 0 (.condBr 2 1 (if nonzero then .notZero (.vreg 1 .int) size else .zero (.vreg 1 .int) size))
          #[⟨1,.int,.use,.early,.reg⟩] regs prefixWorld [] branchWorld
          (.goto (if truth nonzero size ρ then 0 else 1))) ∧
      SameWorldNF F branchWorld world ∧ ∀ k,k ≠ 1 → regs k = ρ k := by
  cases nonzero
  · exact zero_branch_resolved refines (aliases := aliases) (leading := []) (d := 1)
      false size 0 (by decide) (P := fun k => k ≠ 1) (fun _ h => h)
      (companion refines ρ world false size) 2 1
  · exact zero_branch_resolved refines (aliases := aliases) (leading := []) (d := 1)
      true size 0 (by decide) (P := fun k => k ≠ 1) (fun _ h => h)
      (companion refines ρ world true size) 2 1

end Backend.Stock.Proof.ConditionalValues.ResolvedWitness
